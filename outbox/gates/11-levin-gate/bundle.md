## ===== briefs/pass-shelat-ch5-8/gates/11-levin/pack.md =====

# Gate 11 · Levin padding proof

Round 1. Auditor Codex. Draft [PR #286](https://github.com/Shilun-Allan-Li/tcslib/pull/286)
at `a1293a6970b4039a9cf19fd475b9f8cf304a44b3` on branch `codex/pass-shelat-levin-padding`,
targeting `cryptography/pass-shelat-ch2-4` on base `5bcf11aaf08963ab33ce608ea7509e7403e4351a`.
The campaign has since merged #284/#285 (`4a09f399`), which change none of the PR's files; the
maintainer verification ran on a trial merge with that head.

This proof audit covers the formerly admitted `PadQuad.exists_linearTime_gStr`
(`Asymptotic/UniversalPadding.lean`) and everything added to prove it. With it, Lemma 64.3
(`lemma_64_3`) and the conditional Theorem 63.1 (`theorem_63_1`, under its explicit canonizer
hypothesis) print only standard axioms. The source is [PS10], R. Pass and a. shelat, *A Course
in Cryptography*, third edition, January 2010, Theorem 63.1 and Lemma 64.3 (Levin's universal
one-way function, book pp. 63–64), with the padding argument of [Gar26, Lemma 2.3] cited in the
module docstring. `exists_canonizerExp` remains a separate admitted task and is out of scope.

## The padding theorem

Check that `exists_linearTime_gStr` is proved with its original header, for every function `F`
computed by a finite machine in time `C·(n+1)^c`, and that the padded function is computed in
linear time as stated. Follow the route: parameter recovery from the input length (`Parameter`),
binary search for the shifted root (`BinaryRoot`), padding assembly (`Machine`), quantitative
concatenation (`WordTiming`), unary polynomial evaluation (`UnaryPolynomial`) and binary-to-unary
emission (`ClassP/BinaryArith/Unary`). Derive the time bound independently. Test small inputs
(the absorbed finite prefix), the boundary lengths where the recovered parameter changes, empty
data, and inputs whose length is not of the padded form. Confirm that no step's cost is charged
at the wrong argument length.

## Changed infrastructure

`TuringMachine/Build/EmitIterBody` gains `exists_emitIterTM_withFuel` (a supplied fuel machine and
a separate round-count bound) and re-derives `exists_emitIterTM` from it; `TuringMachine/Build/
Primitives` changes `pairMap_computes`. Check that every older statement and definition is
preserved (the statement comparison reports CHANGED only the two `pairSplitAt` theorems below)
and that the moved `nu` block in `UniversalPadding/Parameter` is verbatim, with its new reader
`nu_eq`.

## The maintainer repair commit

The final commit publishes readers so that no touched proof reads another file's definition:
`Turing.safeRun_iff` (`Build/EmitIterEmbed`), and `Turing.pairSplitAt` with three readers
(`Randomized/Build/PairSplit`). `exists_pairSplitTM` and `computesFunInTime_pairSplitAt` are
restated against `pairSplitAt`; they must be the same propositions as before. Check that
the consumers (`Randomized/Primitives`' typed cuts, `UniversalPadding/Machine`) prove what they
did, and that the deleted private `split`/`split_pair` copies left no use behind.

## Rule 10 and evidence

Policy §1, rule 10: no touched statement or proof reads another file's definition. The
verification seals each changed file against its whole import closure, computes the touched
set against the PR base, compares untouched failures with a base control, runs controls and an
explicit-reader scan. Rulings in force: the 52 approved provider pairs (provider reuse,
2026-11-10); F3, a docstring-only change counts as untouched; `PolyExpr.eval` is notation.
Inherited untouched failures stay in the deferred cleanup ledger and are not findings of this
gate unless the PR made them worse. Review the evidence against its stated coverage and the
recorded attempt dispositions, including the segmented and chunked seals and the superseded
attempts.

Inspect the sixteen source files and exact diff, the worker report, the maintainer verification
and policy. Check imports, docstrings with proof sketches, the facades' exports and global
attributes. The PR's 15 module-docstring lines over 100 characters are known; report them as
minor only if you consider them a policy defect.

## Findings delivery

Return `gate11-levin-findings.md` as a Markdown file in this chat. For multiple evidence files,
return a ZIP containing the Markdown and the evidence. The user dispatches and merges.

| # | Severity | File and declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

Use blocker for a false or unusable statement or substantive scope violation, major for a
missing premise, an incomplete machine or timing argument, a forbidden new read in a touched
declaration, or unverifiable necessary evidence, minor for documentation or API defects, and
note for further observations. Report the exact audited head and counts by severity. The gate
closes at zero blockers and zero majors.

## ===== briefs/pass-shelat-ch5-8/gates/11-levin/verification.md =====

# Gate 11 verification

PR #286 head `a1293a6970b4039a9cf19fd475b9f8cf304a44b3` (Codex's production checkpoint
`9ada398e06c00656f96207f5254a826c74130c15` plus one maintainer repair commit), base
`5bcf11aaf08963ab33ce608ea7509e7403e4351a`. Sixteen Lean files change; their blobs are pinned in
[source-head.json](source-head.json). The campaign has since merged #284 and #285 at
`4a09f3993eb9344fc5714610e41ab141a0144db8`, which touches none of the sixteen files. All checks
below ran on a local trial merge of the PR into that campaign head, so they cover the merged
consumers too.

- **Fresh bootstrap (r1).** 1,195/1,195 modules in one fresh tree: 31 PFR sources (copied by git
  blob id) and the 1,164-module merged closure of the library root and campaign `Checks`, on
  375 narrowed Mathlib roots. 0 errors. No compiled object was reused. An 87-module owner tree is
  byte-identical to the full bootstrap. The Mac retained-reference probe is superseded by this
  bootstrap and kept.
- **Repair replays (r2–r4).** After each repair, every module downstream of the changed files was
  rechecked into the same tree: 242, 244 and 244 modules, all rc 0, 0 errors. The first r2 attempt
  stopped at an incorrect edit and is kept as superseded.
- **Generated helpers.** 24 of the 26 renamed helper names are gone; the other two are used only
  by `exists_emitIterTM`. No constant outside the PR's files references any of them.
- **Statements** (`decls2.py` against the base, all 16 files): CHANGED exactly
  `Turing.FinTM.exists_pairSplitTM` and `Turing.FinTM.computesFunInTime_pairSplitAt` (both
  restated against the new `Turing.pairSplitAt`, same proposition); ADDED 21; REMOVED the five
  `nu` declarations, moved verbatim to `UniversalPadding/Parameter.lean` with the reader `nu_eq`.
  `exists_linearTime_gStr` keeps its original header. No existing definition body changed.
- **Axioms.** 182 selected new or changed declarations use only `propext`, `Classical.choice` and
  `Quot.sound`, including `exists_linearTime_gStr`, `lemma_64_3` and `theorem_63_1`. In the ten
  non-facade owners `sorryAx` occurs only in nine untouched `TuringMachine/Build/Primitives`
  theorems resting on its three pre-existing admissions, and in `exists_canonizerExp` (the
  separate canonizer task).
- **Seals.** Every changed file was sealed whole, installing every definition of its full
  TCSlib import closure (abbreviations and `PolyExpr.eval` excepted), with the archived
  instrumenter. `TuringMachine/Build/Primitives` was sealed in three segments (Lean's 100-error
  cap) and the two facades in 1,000-name chunks (stack). Rounds r1–r4 found reads in touched
  declarations F1, F2, F4, F5, F6; the repair commit fixes all of them (see
  [the verification records](../../maintainer/levin-production-2026-11-11/README.md)). At the head,
  **no touched declaration fails**. Every untouched failure is identical at the base control.
  None of them is among the 52 approved provider pairs.
- **Controls.** r1: 38 probes, 160/160 rows as expected; r2–r4: 16 further probes for the newly
  touched files. Old-style reads pass unsealed and fail sealed with exactly one error; the
  published readers pass sealed.
- **Explicit-reader scan.** No foreign-definition item in a touched declaration. Inherited items
  sit in untouched declarations of `TuringMachine/Build/Primitives`, `EmitIterBody`,
  `EmitIterEmbed` and `Randomized/Build/PairSplit`.
- **Rulings applied.** Provider reuse (52 pairs, 2026-11-10). F1/F2 fixed inside #286 with
  `computesFunInTime_pairSplitAt` restated (2026-11-11). F3: a docstring-only change counts as
  untouched; `PadQuad.exists_family`'s read of `FunFamily.ofString`, identical at base, joins the
  inherited failures. F7 was avoided by keeping `split_computes` at its base text.
- **Lint.** No new `sorry`. The repairs add no line over 100 characters. The original PR has 15
  module-docstring lines over 100 characters; the campaign lint does not check line length.

[Verification archive r1–r4](verification.zip) (SHA-256
`622fbc0bef25aad83e54c99fcd6b3f372456c3d8bd2841c8747c5e732b62367f`; its `final/SHA256SUMS`
covers 2,679 files and is indexed by the `DISPOSITIONS*.txt` files).
[362-module source closure at the head](sources.zip) (SHA-256
`cf96a5ba6e886760abc871743699311929720fd5397fde61eb2c2fb228cfc4a9`).

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

## ===== briefs/pass-shelat-ch5-8/gates/11-levin/worker-report.md =====

# Levin production checkpoint

Draft [PR #286](https://github.com/Shilun-Allan-Li/tcslib/pull/286) at 9ada398e06c00656f96207f5254a826c74130c15
contains the integrated proof of PadQuad.exists_linearTime_gStr. The original
header is preserved. Six supporting modules separate parameter recovery,
binary search, padding assembly, quantitative concatenation, unary polynomial
evaluation and binary-to-unary emission. The existing facades export them.

All sixteen native module checks pass at the checkpoint source, including
the thirteen changed files, asymptotic facade, library root and campaign
Checks. All 174 selected new or changed stored declarations use standard
Lean axioms. The actual padding theorem, lemma_64_3 and the conditional
theorem_63_1 also print only standard axioms.

The raw comparison and probe failures are retained. Generalizing the core
proofs changes 26 generated proof-helper identities. The retained-reference
probe needs actual Lean Name values for numeric private components before
that dependency check can finish. The production seal review, controls,
final reader scan and Codex audit also remain. The provider reuse ruling
is approved. The canonizer proof is a separate task.

Resume in the managed worktree at
/Users/seyoonr/.codex/worktrees/ps-levin-padding/tcslib-pass-shelat-ch2-4.
The local native tree and tools are under
/private/tmp/tcslib-levin-proofs.g9J5YEGr/production. The two archives below
preserve the source and evidence if the temporary tree is lost. Every
maintainer native check has finished.

[Checked source](production-source.zip) has SHA-256 `830c79b0f09ebaa45b12b30334b2758be6f40a81fcc86a2f40d96a6e1154ccf2`.
[Native logs and remaining checks](production-checkpoint.zip) have SHA-256 `3c92610aca6865ef182a4b933ebcf34629e1718856b2115d78ecc5a269f594fd`.

The completed Claude efficiency fill is in draft PR #285. Codex Gate 10
is [ready to dispatch](../../gates/10-efficiency/dispatch.md).
PR #284 remains clear for Seyoon to merge at its audited source.

**Not yet clear to merge — Levin production seals, dependency verification and external audit are pending.**

## ===== briefs/pass-shelat-ch5-8/maintainer/proof-prerequisites-2026-11-10/provider-ruling.md =====

# Levin provider reuse ruling

Seyoon approved reuse of the existing provider proofs for the Levin padding proof on 2026-11-10. Seal the new proof and retain every inherited finding in the deferred cleanup ledger. The comparison is declaration-specific. Of 52 historical diagnostic/declaration pairs, 49 also occur in the efficiency issue-time set. The three further pairs are SEAL-0012 on `Complexity.polyTimeComputable_emitIter` and SEAL-0017/0018 on `PrefixByLength.goes_doubled`. The complete names are in [the comparison](provider-comparison.json).

Codex is selected for the integrated Levin audit and will return findings Markdown in chat. Continue source integration and the ordinary new-proof checks with these provider proofs cited through their public interfaces.

**Ready to run**

## ===== briefs/pass-shelat-ch5-8/maintainer/levin-production-2026-11-11/README.md =====

# Levin padding (#286): production verification, 2026-11-11

**Status: all touched-declaration reads repaired (head `a1293a6970b4039a9cf19fd475b9f8cf304a44b3`); Gate 11 (Codex) staged.**

## Pins
- PR head `9ada398e06c00656f96207f5254a826c74130c15`, PR base `5bcf11aaf08963ab33ce608ea7509e7403e4351a`.
- Verified on a local trial merge `562ad0cacbc718ed3d932e509822cfa24087acfa` (parents `9ada398e…`, campaign
  `4a09f3993eb9344fc5714610e41ab141a0144db8`; never pushed). The 13 PR files are byte-identical to the PR head.
- Campaign later moved to `a3dcb21c` (records only, 0 Lean files).
- Evidence: `levin-production-verification.zip`, SHA-256
  `2c35f989332f6aa5d77a66b0f35f6b058943b1322f234784f0d4b4812115d63c`; its `SHA256SUMS` (1,669 files) is
  `evidence-SHA256SUMS` here, SHA-256 `a07afff2a771b8274601c33d80fd5a2072b789d90617fab824b45a587dcc9057`.
  Index: `DISPOSITIONS.txt`, `provenance.json`.

## Results
- **Bootstrap:** 1,195/1,195 modules (31 PFR copied by blob id + 1,164 merged closure, 375 Mathlib roots),
  0 errors, one fresh tree. `sorry` in the 13 files unchanged (3 in `TuringMachine/Build/Primitives`, 1 in
  `Universal`: `exists_canonizerExp`). An 87-module owner tree is byte-identical. Hand-off item 5 (reuse) is
  resolved by the fresh bootstrap; the Mac retained-reference probe is kept as superseded.
- **Generated helpers:** 24 of 26 changed helper names are gone; the remaining 2 are used only by
  `exists_emitIterTM`. No outside reference.
- **Statements (`decls2.py` vs 5bcf11aa):** 16 added, 5 removed (the `nu` block moved verbatim to
  `Parameter.lean`, plus reader `nu_eq`), 0 changed. No existing `def` body changed.
- **Axioms:** `exists_linearTime_gStr`, `lemma_64_3`, `theorem_63_1` use only `propext`, `Classical.choice`,
  `Quot.sound`. `sorryAx` only in 9 untouched Primitives theorems on 3 pre-existing sorries and in
  `exists_canonizerExp`.
- **Seals (full import-closure definitions, minus notation):** touched declarations clean except F1–F3; every
  untouched failure is identical at base; none touches the 52 approved provider pairs.
- **Controls:** 38 probes, 160/160 rows as expected.
- **Explicit-reader scan:** 531 foreign-definition items, none in a touched declaration.

## Findings (attribution confirmed by single-name unseal)
- **F1.** `Turing.FinTM.exists_emitIterTM_withFuel` (`TuringMachine/Build/EmitIterBody.lean`, new) destructures
  `Turing.SafeRun` (`Build/EmitIterEmbed.lean`) with `obtain ⟨hrun, hsafe⟩`. Moved from base
  `exists_emitIterTM`. Needs a published `SafeRun_iff` in `EmitIterEmbed.lean` (a file outside #286).
- **F2.** `PadQuad.linear_split` (`UniversalPadding/Machine.lean`, new private) proves `Linear split` from
  `computesFunInTime_pairSplitAt` by unfolding its compiler-generated matcher (`Randomized/Primitives.lean`, a
  file outside #286). Needs a named split function with case lemmas in `Randomized/Primitives.lean`.
- **F3.** `PadQuad.exists_family` (`UniversalPadding.lean`) changed only in its docstring; reads
  `FunFamily.ofString` identically at base; the reader `FunFamily.ofString_inLen_eval` exists. Ruling needed.

## Deviations
Primitives sealed in 3 segments (100-error cap); the two facade seals chunked at 1,000 names (stack); PFR copied
because symlinked sources are rejected. Failed attempts retained in the evidence.

## Repairs and re-verification (r2–r4)

Rulings (Seyoon, 2026-11-11): F1/F2 fixed inside #286 with `computesFunInTime_pairSplitAt`
restated; F3 counts as untouched. One maintainer commit `a1293a69` on
`codex/pass-shelat-levin-padding` holds the final repair (patch `fix-r4.patch`, SHA-256
`ef659c92688d8f437784544f195c74211d5d70be2f10edc0008a3938b6774edb`).

- **r2** (F1/F2 patch): replay 242/242 (a first attempt stopped at a wrong `body_round` edit,
  kept). F1, F2 cleared. New **F4**: the restated `computesFunInTime_pairSplitAt` still read
  PairSplit's private matcher through `exists_pairSplitTM` (as at base).
- **r3** (`pairSplitAt` moved into `Randomized/Build/PairSplit`): replay 244/244. F4 cleared. New
  **F5** (`exists_pairSplitTM` applied `ComputesFunInTime` as a function, as at base), **F6**
  (private `polyTimeComputable_pairSplitAt` newly read the moved definition), **F7**
  (`simp [MultiTapeTM.initCfg, Cfg.init]` in `split_computes`, touched by the restatement).
- **r4**: `exists_pairSplitTM` through `computesFunInTime_iff` (F5); the private lemma restated
  as `PolyTimeComputable pairSplitAt`, its users through `pairSplitAt_pairEncode` (F6);
  `split_computes` back at its base text, so F7 is an inherited untouched line. Replay 244/244.
  Seals: 0 touched failures in all changed files; untouched failures identical at base.
  Attribution clears F5/F6. Controls pass. Scan: no foreign-definition item in a touched
  declaration. Statements: CHANGED `exists_pairSplitTM`, `computesFunInTime_pairSplitAt`;
  ADDED 21; REMOVED the 5 moved `nu` declarations. 182 selected declarations, standard axioms.

Evidence r1–r4: `gates/11-levin/verification.zip`, SHA-256
`622fbc0bef25aad83e54c99fcd6b3f372456c3d8bd2841c8747c5e732b62367f` (r2 `8e89a4f0…`, r3
`1a67be51…` zips are subsets and stay local).

## ===== TCSlib/Complexity/ClassP/BinaryArith.lean =====

/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.ClassP.BinaryArith.Iterate
import TCSlib.Complexity.ClassP.BinaryArith.Basic
import TCSlib.Complexity.ClassP.BinaryArith.AddSub
import TCSlib.Complexity.ClassP.BinaryArith.Mul
import TCSlib.Complexity.ClassP.BinaryArith.Div
import TCSlib.Complexity.ClassP.BinaryArith.ModPow
import TCSlib.Complexity.ClassP.BinaryArith.Jacobi
import TCSlib.Complexity.ClassP.BinaryArith.Words
import TCSlib.Complexity.ClassP.BinaryArith.Loops
import TCSlib.Complexity.ClassP.BinaryArith.Unary
import TCSlib.Complexity.ClassP.BinaryArith.PrimeFind
import TCSlib.Complexity.ClassP.BinaryArith.DetModMath
import TCSlib.Complexity.ClassP.BinaryArith.DetMod

/-!
# Binary arithmetic in polynomial time

Binary arithmetic on `Nat.bits` words (pairs via `Turing.pairEncode`) as polynomial-time
functions: infrastructure for [AB09 §7.2], plus [AB09, Exercise 7.3] and [AB09, §7.2.2].

## Contents

* `Iterate` — iterating a polynomial-time step polynomially often is polynomial-time.
* `Basic` — normalization, last bit, zero-padded bit pairs and finite-state scans.
* `AddSub` — comparison (`<`, `≤`, `=`, also as languages in `P`), addition, subtraction.
* `Mul` — multiplication; word reversal.
* `Div` — quotient and remainder.
* `ModPow` — modular exponentiation [AB09, Exercise 7.3]; the gcd.
* `Jacobi` — the Jacobi symbol for odd moduli [AB09, §7.2.2].
* `Words` — lists of words: map, zip and count loops.
* `Loops` — the counted loop, unary numbers, list lookup, word equality, unary multiplication
  and cutting into blocks.
* `Unary` — canonical binary width bounds and a finite binary-to-unary converter.
* `PrimeFind` — the least prime above `2^{⌈log₂ 2n⌉}`, for unary `n`.
* `DetModMath` — the elimination, rotation and zero-column identities over `ZMod p`.
* `DetMod` — the determinant over `ZMod p` by Gaussian elimination.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.2; Exercise 7.3.)
-/

## ===== TCSlib/Complexity/ClassP/BinaryArith/Unary.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.ClassP.BinaryArith.Loops
import TCSlib.Complexity.TuringMachine.Build.EmitIterBody
import Mathlib.Analysis.SpecificLimits.Normed

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Binary width bounds and conversion to unary

The width of a canonical binary word bounds powers of two and fixed polynomials in that width by linear functions of its value. A finite emitting loop converts an arbitrary binary word to unary with a bound polynomial in the raw width times two to that width.

## Main definitions

The private countdown step takes a normalized binary predecessor, and its emission is one token at a positive state.

## Main results

* `polyTimeComputable_powerOfTwo` computes two to the input width in binary.
* `two_pow_width_le` and `exists_pow_width_bound` bound canonical widths.
* `exists_binaryToUnary` gives the finite conversion machine and its running time.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2, multitape machines, and §7.2, efficient arithmetic.)
-/

open Complexity Complexity.BinArith Complexity.LogProg Turing Turing.FinTM Filter

attribute [local irreducible] PolyTimeComputable FinTM.ComputesInTime FinTM.ComputesFunInTime
attribute [local irreducible] pairEncode BinArith.sub transduce

namespace Complexity.BinArith

/-- The binary word for the power of two indexed by a word's length. -/
theorem polyTimeComputable_powerOfTwo :
    PolyTimeComputable (fun z : List Bool => Nat.bits (2 ^ z.length)) := by
  let δ := fun (_ : Unit) (_ : Bool) => ()
  let emit := fun (_ : Unit) (_ : Bool) => some false
  have hzero (z : List Bool) : transduce δ emit () z = List.replicate z.length false := by
    induction z with
    | nil => rw [transduce_nil]; rfl
    | cons b z ih => rw [transduce_cons, show δ () b = () from rfl, ih]; rfl
  simpa only [hzero, bits_two_pow_eq_replicate] using
    (polyTimeComputable_transduce δ emit ()).append (polyTimeComputable_const [true])


/-- The binary width is small enough that its power-of-two bound is at most
twice the represented number plus two. -/
theorem two_pow_width_le (m : ℕ) : 2 ^ m.bits.length ≤ 2 * (m + 1) := by
  rw [Nat.size_eq_bits_len]
  cases he : m.size with
  | zero => simp only [pow_zero]; omega
  | succ k =>
      have h : 2 ^ k ≤ m := Nat.lt_size.mp (by omega)
      rw [pow_succ]
      omega

/-- Every fixed polynomial in the binary width is bounded by a linear
function of the represented number.

**Proof sketch.** A polynomial in the width is eventually at most two
to that width. Absorb the finitely many smaller widths into the constant
and apply the binary width bound. -/
theorem exists_pow_width_bound (e : ℕ) :
    ∃ A : ℕ, ∀ m : ℕ, (m.bits.length + 1) ^ e ≤ A * (m + 1) := by
  have hlim := isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) e
    (by norm_num : 1 < (2 : ℝ))
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (Asymptotics.isLittleO_iff.mp hlim (by norm_num : (0 : ℝ) < 1))
  refine ⟨N ^ e + 4, fun m => ?_⟩
  by_cases hm : N ≤ m.bits.length + 1
  · have h := hN _ hm
    have hnonneg : 0 ≤ ((m.bits.length + 1 : ℕ) : ℝ) ^ e :=
      pow_nonneg (Nat.cast_nonneg _) _
    have htwo : 0 ≤ (2 : ℝ) ^ (m.bits.length + 1) := by positivity
    simp only [Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg htwo, one_mul] at h
    have hpow : (m.bits.length + 1) ^ e ≤ 2 ^ (m.bits.length + 1) := by exact_mod_cast h
    have hwidth := two_pow_width_le m
    rw [pow_succ] at hpow
    rw [Nat.add_mul]
    omega
  · have h := Nat.pow_le_pow_left (by omega : m.bits.length + 1 ≤ N) e
    have hmul := Nat.mul_le_mul_left (N ^ e) (by omega : 1 ≤ m + 1)
    rw [Nat.mul_one] at hmul
    rw [Nat.add_mul]
    omega

/-- The next state of the unary emission loop is the normalized predecessor. -/
private def predWord (z : List Bool) : List Bool := Nat.bits (bitsVal z - 1)

/-- The predecessor is binary subtraction by one after normalization. -/
private theorem polyTimeComputable_predWord : PolyTimeComputable predWord := by
  convert polyTimeComputable_sub.comp
    (polyTimeComputable_normBits.pairEncode (polyTimeComputable_const (Nat.bits 1))) using 1
  funext z
  simp only [predWord, Function.comp_apply, sub_pairEncode]

/-- The loop emits one token exactly when its binary state is positive. -/
private def emitToken (z : List Bool) : List Bool := if z.any id then [true] else []

/-- A scan for a set bit decides whether to emit the single token. -/
private theorem polyTimeComputable_emitToken : PolyTimeComputable emitToken := by
  simpa only [emitToken] using polyTimeComputable_ite polyTimeComputable_any
    (polyTimeComputable_const [true]) (polyTimeComputable_const [])

/-- The orbit's value is the initial value minus the number of decrements. -/
private theorem predWord_iterate_value (z : List Bool) (i : ℕ) :
    bitsVal (predWord^[i] z) = bitsVal z - i := by
  induction i with
  | zero => simp only [Function.iterate_zero_apply, Nat.sub_zero]
  | succ i ih =>
      rw [Function.iterate_succ_apply', predWord, bitsVal_bits, ih]
      omega

/-- Each orbit state has at most the original word's binary width. -/
private theorem predWord_iterate_length (z : List Bool) (i : ℕ) :
    (predWord^[i] z).length ≤ z.length := by
  cases i with
  | zero => simp only [Function.iterate_zero_apply, le_refl]
  | succ i =>
      rw [Function.iterate_succ_apply', predWord, predWord_iterate_value]
      exact length_bits_le_of_le z (by omega) le_rfl

/-- On the orbit a token is emitted during exactly the positive countdown
rounds. -/
private theorem emitToken_iterate (z : List Bool) (i : ℕ) :
    emitToken (predWord^[i] z) = if i < bitsVal z then [true] else [] := by
  by_cases hi : i < bitsVal z
  · have hzero : (predWord^[i] z).any id ≠ false := by
      intro h
      have hv := (bitsVal_eq_zero_iff _).mpr h
      rw [predWord_iterate_value] at hv
      omega
    simp only [emitToken, if_pos hi, Bool.eq_true_of_not_eq_false hzero, ↓reduceIte]
  · have hzero := (bitsVal_eq_zero_iff (predWord^[i] z)).mp (by
      rw [predWord_iterate_value]
      omega)
    simp only [emitToken, if_neg hi, hzero, Bool.false_eq_true, ↓reduceIte]

/-- The first R rounds of an initial countdown of v emit exactly
the smaller of R and v tokens. -/
private theorem unary_chunks (R v : ℕ) :
    (List.range R).flatMap (fun i => if i < v then [true] else []) =
      List.replicate (min R v) true := by
  induction R with
  | zero => simp
  | succ R ih =>
      rw [List.range_succ, List.flatMap_append, ih, List.flatMap_singleton]
      by_cases h : R < v
      · rw [if_pos h, Nat.min_eq_left h.le, Nat.min_eq_left (Nat.succ_le_of_lt h)]
        change List.replicate R true ++ List.replicate 1 true = _
        rw [← List.replicate_add]
      · rw [if_neg h, List.append_nil, Nat.min_eq_right (by omega : v ≤ R),
          Nat.min_eq_right (by omega : v ≤ R + 1)]

/-- A finite emitter converts binary to unary. Its time is polynomial in the
binary width times two to that width.

**Proof sketch.** The fuel machine emits the binary representation of two to
the input width. Instantiate the existing emit-iteration body with binary
predecessor and a token on each positive orbit state. The width remains
bounded throughout the orbit, and the binary fuel covers every possible
input value. -/
theorem exists_binaryToUnary : ∃ (M : FinTM Bool) (C c : ℕ),
    M.ComputesFunInTime (fun w => List.replicate (bitsVal w) true)
      (fun n => C * (n + 1) ^ c * (2 ^ n + 2)) := by
  have hfuel := polyTimeComputable_powerOfTwo
  obtain ⟨G, A, a, hG⟩ := (polyTimeComputable_iff _).1 polyTimeComputable_predWord
  obtain ⟨E, B, b, hE⟩ := (polyTimeComputable_iff _).1 polyTimeComputable_emitToken
  obtain ⟨F, K, k, hF⟩ := (polyTimeComputable_iff _).1 hfuel
  obtain ⟨M, C, c, hM⟩ := exists_emitIterTM_withFuel G E F predWord emitToken A a B b K k
    (fun n => 2 ^ n) hG hE hF 1 1 (fun w i => by
      simpa only [one_mul, pow_one] using (predWord_iterate_length w i).trans (Nat.le_succ _))
  refine ⟨M, C, c, (computesFunInTime_iff _ _ _).2 fun w => ?_⟩
  have h := (computesFunInTime_iff _ _ _).1 hM w
  rw [List.flatMap_congr (fun i _ => emitToken_iterate w i), unary_chunks,
    Nat.min_eq_right (by have := bitsVal_lt_two_pow w; omega)] at h
  exact h


end Complexity.BinArith

## ===== TCSlib/Complexity/Randomized.lean =====

/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.SchwartzZippel
import TCSlib.Complexity.Randomized.ErrorReduction
import TCSlib.Complexity.Randomized.Classes
import TCSlib.Complexity.Randomized.Adleman
import TCSlib.Complexity.Randomized.SipserGacs
import TCSlib.Complexity.Randomized.PolyTimeModel
import TCSlib.Complexity.Randomized.PTM
import TCSlib.Complexity.Randomized.Inclusions
import TCSlib.Complexity.Randomized.PTMEquiv
import TCSlib.Complexity.Randomized.Median
import TCSlib.Complexity.Randomized.PrimalityMath
import TCSlib.Complexity.Randomized.Primality
import TCSlib.Complexity.Randomized.AlgCircuit
import TCSlib.Complexity.Randomized.RandomBits
import TCSlib.Complexity.Randomized.Fingerprint
import TCSlib.Complexity.Randomized.ZeroPEval
import TCSlib.Complexity.Randomized.ZeroPRun
import TCSlib.Complexity.Randomized.ZeroP
import TCSlib.Complexity.Randomized.ZeroPPIT
import TCSlib.Complexity.Randomized.MatchingMath
import TCSlib.Complexity.Randomized.Matching
import TCSlib.Complexity.Randomized.ExpectedTime
import TCSlib.Complexity.Randomized.Coins
import TCSlib.Complexity.Randomized.ZPPEquiv
import TCSlib.Complexity.Randomized.ZPPHosts
import TCSlib.Complexity.Randomized.ZPPHostsClasses
import TCSlib.Complexity.Randomized.Reductions
import TCSlib.Complexity.Randomized.NPPoly
import TCSlib.Complexity.Randomized.Yap
import TCSlib.Complexity.Randomized.DirectedWalk
import TCSlib.Complexity.Randomized.BPPHard
import TCSlib.Complexity.Randomized.BPLInPCount
import TCSlib.Complexity.Randomized.BPLInPWords
import TCSlib.Complexity.Randomized.BPLInP
import TCSlib.Complexity.Randomized.RandomWalkCover
import TCSlib.Complexity.Randomized.RandomWalkMixing
import TCSlib.Complexity.Randomized.RandomWalkMixingPad
import TCSlib.Complexity.Randomized.UniformSample
import TCSlib.Complexity.Randomized.BiasedCoin
import TCSlib.Complexity.Randomized.BiasedCoinHalting
import TCSlib.Complexity.Randomized.SpaceAmplifyPolyCode
import TCSlib.Complexity.Randomized.SpaceAmplifyPolyMachine
import TCSlib.Complexity.Randomized.SpaceAmplifyPolyRun
import TCSlib.Complexity.Randomized.SpaceAmplifyPoly
import TCSlib.Complexity.Randomized.ZeroPReduce
import TCSlib.Complexity.Randomized.BPPAmplify
import TCSlib.Complexity.Randomized.RPExpected
import TCSlib.Complexity.Randomized.BPOperator
import TCSlib.Complexity.Randomized.AlgCircuitExample
import TCSlib.Complexity.Randomized.QuasiPolyHierarchy
import TCSlib.Complexity.Randomized.BPPEqP
import TCSlib.Complexity.Randomized.BPTIMEThreshold
import TCSlib.Complexity.Randomized.Space
import TCSlib.Complexity.Randomized.SpaceAmplify
import TCSlib.Complexity.Randomized.SpaceAmplifyRun
import TCSlib.Complexity.Randomized.RandomWalk
import TCSlib.Complexity.Randomized.RandomWalkHitting
import TCSlib.Complexity.Randomized.RandomWalkPad
import TCSlib.Complexity.Randomized.UPath
import TCSlib.Complexity.Randomized.UPathMachine
import TCSlib.Complexity.Randomized.UPathLoops
import TCSlib.Complexity.Randomized.UPathParse
import TCSlib.Complexity.Randomized.UPathSearch
import TCSlib.Complexity.Randomized.UPathWalk
import TCSlib.Complexity.Randomized.UPathRL
import TCSlib.Complexity.Randomized.PolyExpr
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Complexity.Randomized.NonUniform
import TCSlib.Complexity.Randomized.Primitives
import TCSlib.Complexity.Randomized.UnaryPolynomial
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Complexity.Randomized.Repetition

/-!
# Randomized Computation

Arora–Barak Chapter 7 (Randomized Computation): the model-free
probabilistic tools, and the chapter's complexity classes and theorems in
the certificate view of [AB09, Def 7.3], relative to an abstract efficiency
notion (`Randomized.VerifierModel`) standing in for polynomial-time Turing
machines.

## Contents

- `Randomized.SchwartzZippel`: the Schwartz–Zippel lemma in Arora–Barak's
  form ([AB09, Lem 7.5]), restated from Mathlib's
  `MvPolynomial.schwartz_zippel_totalDegree`.
- `Randomized.ErrorReduction`: concentration for i.i.d. Boolean trials (Hoeffding form of the
  Chernoff bound [AB09, Cor A.15]) and the majority-vote error bound that is the calculation
  inside the error-reduction theorem ([AB09, Thm 7.10]).
- `Randomized.Classes`: verifier-style `BPP`/`RP`/`coRP`/`ZPP`
  ([AB09, Defs 7.2/7.3/7.6/7.7]), `ZPP = RP ∩ coRP` ([AB09, Thm 7.8]), and
  error reduction at the class level ([AB09, Lem 7.9, Thm 7.10]).
- `Randomized.Adleman`: `BPP ⊆ P/poly` ([AB09, Thm 7.14]), concluding in
  `Language.InPPoly` from `CircuitComplexity.PPoly`.
- `Randomized.SipserGacs`: certificate-style `Σ₂ᵖ`/`Π₂ᵖ` and
  `BPP ⊆ Σ₂ᵖ ∩ Π₂ᵖ` ([AB09, Thm 7.15]).
- `Randomized.PolyTimeModel`: the instantiation of the abstract verifier
  model by genuine polynomial-time machines (`Complexity.P`), discharging
  the closure hypotheses and connecting `Σ₂` to `Complexity.SigmaP 2`.
- `Randomized.PTM`: probabilistic Turing machines as binary-choice machines read
  probabilistically; `BPTIME`, `BPP_PTM`, `RTIME`, `RP_PTM`, `coRP_PTM`
  ([AB09, Def 7.1, Def 7.2, Def 7.6]).
- `Randomized.Inclusions`: `P ⊆ BPP`, `RP ⊆ NP`, `RP, coRP ⊆ BPP`, `BPP ⊆ EXP`,
  `NP = P ⇒ BPP = P`, `3SAT ∈ BPP ⇒ PH = Σ₂ᵖ` ([AB09, §7.1, §7.3, §7.5.1]) and RP error
  reduction ([AB09, Exercise 7.4]).
- `Randomized.PTMEquiv`: the PTM classes equal the certificate classes over polynomial-time
  verifiers ([AB09, Def 7.2 ≡ Def 7.3]).
- `Randomized.Median`: `FindKthElement` and its expected number of comparisons
  ([AB09, §7.2.1, Claim 7.4]).
- `Randomized.PrimalityMath`, `Randomized.Primality`: Solovay–Strassen; `PRIMES ∈ coRP`
  ([AB09, §7.2.2]).
- `Randomized.AlgCircuit`: algebraic circuits, their polynomials and degree, `ZEROP`
  ([AB09, §7.2.3]).
- `Randomized.RandomBits`: shared counting lemmas over random strings (conditioning on a
  prefix, the union bound) and numbers read off blocks of fair coins.
- `Randomized.Fingerprint`: the fingerprinting test for `ZEROP` and its error analysis
  ([AB09, §7.2.3]).
- `Randomized.ZeroPEval`, `Randomized.ZeroPRun`: the polynomial-time evaluator of encoded
  algebraic circuits modulo `k`.
- `Randomized.ZeroP`, `Randomized.ZeroPPIT`: `ZEROP ∈ coRP` and polynomial identity testing
  in `coRP` ([AB09, §7.2.3]).
- `Randomized.MatchingMath`, `Randomized.Matching`: Edmonds matrix, Lovász's test, bipartite
  perfect matching in `RP` ([AB09, §7.2.4]).
- `Randomized.ExpectedTime`: expected running time, `ZTIME`, `ZPP_PTM`
  ([AB09, §7.3, Def 7.7]) and Markov truncation ([AB09, §7.4.2]).
- `Randomized.Coins`: biased coins from fair coins and von Neumann's extractor
  ([AB09, Lemma 7.12, Lemma 7.13]).
- `Randomized.ZPPEquiv`, `Randomized.ZPPHosts`, `Randomized.ZPPHostsClasses`: `ZPP` in its
  expected-time, abort and certificate forms, and `ZPP = RP ∩ coRP` for Def 7.7
  ([AB09, Theorem 7.8, Exercise 7.6]).
- `Randomized.Reductions`: randomized reductions and `BP·NP` ([AB09, Def 7.16, Def 7.17]).
- `Randomized.NPPoly`: `NP/poly` and `BP·NP ⊆ NP/poly` ([AB09, Exercise 7.7]).
- `Randomized.Yap`: Yap's theorem (`coNP ⊆ NP/poly ⇒ PH = Σ₃ᵖ`) and [AB09, Exercise 7.8].
- `Randomized.DirectedWalk`: the random walk on a directed graph can need Ω(2ⁿ) steps
  [AB09, Exercise 7.10].
- `Randomized.BPPHard`: `⟨M, x, 1ᵗ⟩` with acceptance probability ≥ 2/3 is BPP-hard
  [AB09, §7.5.3, p. 138].
- `Randomized.BPLInPCount`, `Randomized.BPLInPWords`, `Randomized.BPLInP`: `BPL ⊆ P` by an exact
  dynamic program over configurations [AB09, Exercise 7.9].
- `Randomized.RandomWalkCover`: connectivity, bipartiteness and the bipartite double cover for
  regular multigraphs; even-length walks of length `2n` between any two vertices.
- `Randomized.RandomWalkMixing`, `Randomized.RandomWalkMixingPad`: contraction to uniform,
  uniqueness of the stationary distribution, visit frequency, and the self-loop regularization
  transfer [AB09, Exercise 7.11(b), (e)].
- `Randomized.UniformSample`: uniform sampling from `[N]` with coin tosses [AB09, Exercise 7.1].
- `Randomized.BiasedCoin`, `Randomized.BiasedCoinHalting`: ρ-coin PTMs; an uncomputable ρ decides an
  undecidable language in polynomial time [AB09, Exercise 7.5].
- `Randomized.SpaceAmplifyPolyCode`, `…Machine`, `…Run`, `Randomized.SpaceAmplifyPoly`: BPL and RL
  error reduction to `2^{-n^d}` in logarithmic space [AB09, §7.7, p. 139].
- `Randomized.ZeroPReduce`: the polynomial-time reduction PIT ≤ₚ ZEROP and closure of RP/coRP under
  ≤ₚ [AB09, §7.2.3].
- `Randomized.BPPAmplify`: Lemma 7.9 and Theorem 7.10 for polynomial-time PTMs and the
  polynomial-time verifier model; any constant above `1/2` gives BPP [AB09, §7.4.1].
- `Randomized.RPExpected`: expected polynomial time gives the same RP and coRP [AB09, §7.4.2].
- `Randomized.BPOperator`: the `BP·` operator; `BP·P = BPP` and `BP·NP` agrees with Def 7.17
  [AB09, Chapter notes].
- `Randomized.AlgCircuitExample`: `∏(1 + xᵢ)` has a circuit with `2n` operations but `2ⁿ` monomials
  [AB09, §7.2.3, p. 129].
- `Randomized.QuasiPolyHierarchy`: `P ⊊ DTIME(n^{log n})` via a time-constructible quasi-polynomial
  budget.
- `Randomized.BPPEqP`: if `BPP = P` then `BPP ⊊ DTIME(n^{log n})` and BPP has a complete problem
  [AB09, §7.5, §7.5.3].
- `Randomized.BPTIMEThreshold`: any constant threshold in `(1/2, 1)` gives the same
  `BPTIME(T(n))` [AB09, §7.1, p. 125].
- `Randomized.Space`, `Randomized.SpaceAmplify`, `Randomized.SpaceAmplifyRun`: randomized
  space, `BPL`, `RL`, `RL ⊆ NL ⊆ P`, error reduction in log space ([AB09, §7.7, Def 7.18]).
- `Randomized.RandomWalk`, `Randomized.RandomWalkHitting`, `Randomized.RandomWalkPad`:
  random walks on regular multigraphs and their hitting times ([AB09, Exercise 7.11]).
- `Randomized.UPath`, `Randomized.UPathMachine`, `Randomized.UPathLoops`,
  `Randomized.UPathParse`, `Randomized.UPathSearch`, `Randomized.UPathWalk`,
  `Randomized.UPathRL`: `UPATH ∈ RL` ([AB09, Theorem 7.19]).

The Pass–shelat ch. 2–4 layer (`PassShelatChapter2-4Plan.md`; namespace `Complexity`):
probabilistic polynomial-time machines with explicit coin and advice polynomials, their
closure calculus, and the repetition lemma.

- `Randomized.PolyExpr`: syntactic polynomials `Complexity.PolyExpr` for every length and
  budget (evaluation, substitution, monotonicity, the normal-form majorant).
- `Randomized.PPT`: the structure `Complexity.NUPPT` (PPT [PS10, Definition 23.4] with
  worst-case time [PS10, Definition 23.5], computing with probability one [PS10, Definition
  24.6], non-uniform PPT in the advice form [PS10, Definition 26.8]) and the subtype
  `Complexity.PPT`.
- `Randomized.NonUniform`: the two formulations of Definition 26.8, uniformity lemmas, and
  the bridge from `Turing.FinTM.DecidesWithAdviceInTime`.
- `Randomized.Primitives`: coin splitting, unary multiplication, the unary evaluator and the
  typed coin cuts.
- `Randomized.UnaryPolynomial` — unary polynomial evaluation in time proportional
  to the input and output lengths.
- `Randomized.Closure`: the closure calculus of non-uniform PPTs.
- `Randomized.Repetition`: the repetition lemma `polyTimeComputable_iterateFind` and its
  iteration variants.

All entries, and the files they describe, cite the printed book's (2009) numbering.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
-/

## ===== TCSlib/Complexity/Randomized/Build/PairSplit.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Data.List.Induction
import Mathlib.Tactic.DeriveFintype
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.TuringMachine.Simulation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The coin-splitting machine

The explicit finite machine behind `Turing.FinTM.computesFunInTime_pairSplitAt`
(`TCSlib.Complexity.Randomized.Primitives`): on a pair `⟨u, b⟩` it outputs the pair
`⟨b.take |u|, b.drop |u|⟩`, on a malformed word it outputs `[]`, and it halts within
`5 (n + 1)` steps on every input of length `n`. This is the primitive by which a reduction
cuts its coin string at a unary length and uses the two segments as independent uniform
strings ([PS10, §2.1], implicit in every reduction of chapters 2–4; foundation decision D11
of `PassShelatChapter2-4Plan.md`: the two new primitives are built in the `Build/` style).

## Construction (DESIGN.md §2.4)

One work tape and six control modes (nine states), in the idiom of the private buffered extractor of
`TCSlib.Complexity.TuringMachine.Build.Primitives` (copied privately, never edited).

* **Phase 1, `parse`.** The buffered aligned parser: aligned two-bit blocks `00`/`11` of the
  doubled first component are undoubled onto the work tape without emitting anything; the
  aligned separator `01` ends the phase; the end of the input inside a block or the aligned
  block `10` halts the machine — with empty output, since nothing has been emitted yet and
  the output tape is append-only (a malformed word must produce exactly `[]`).
* **Phase 2, `rewind`.** The work head walks back to the origin.
* **Phase 3, `copy`/`dup`.** A copy scan of the second component `b`: while the work head
  reads a stored symbol of `u` and the input head reads a bit `c` of `b`, the machine emits
  `c` twice (`dup` remembers `c` for the second emission) and advances both heads; exactly
  `min |u| |b|` bits of `b` are doubled, i.e. the first component `b.take |u|` of the output
  pair (`List.take` saturates when `b` is shorter than `u`).
* **Phase 4, `sep`/`tail`.** When the stored `u` or the input is exhausted the machine
  emits the separator `01` and copies the rest of the input verbatim (empty when `b` is
  shorter than `u`), then halts at the right blank.

Every phase is accounted for by an explicit step ledger: the parser costs two steps per
block, the rewind `|u| + 1`, the copy scan two steps per doubled bit, the separator two,
the tail one per remaining bit plus one; the total is at most `5 (n + 1)`.

The parse phase (phases 1 and 2) is public, for every one-tape machine whose table agrees with
the parser at its states (namespace `Turing.PairParse`): the unary-multiplication machine of
`TCSlib.Complexity.Randomized.Build.UnaryMul` uses it too.

## Main definitions

* `Turing.pairSplitAt` — the split function `⟨u, b⟩ ↦ ⟨b.take |u|, b.drop |u|⟩` (`[]` off pairs),
  read through `Turing.pairSplitAt_pairEncode`, `Turing.pairSplitAt_of_pairDecode_eq_some` and
  `Turing.pairSplitAt_of_pairDecode_eq_none`.
* `Turing.PairParse.cfg` — the one-buffer configurations of a one-tape machine (field equations
  by `simps`). The machine itself is private; its result is an existence statement over
  `Turing.FinTM Bool`.

## Main results

* `Turing.FinTM.exists_pairSplitTM` — a finite machine computes `Turing.pairSplitAt`,
  `⟨u, b⟩ ↦ ⟨b.take |u|, b.drop |u|⟩` (and `[]` on malformed words), within `5 (n + 1)` steps.
* `Turing.PairParse.parse_first`, `parse_block`, `rewind_run` — the buffered aligned parser:
  one half block, one aligned block, and the rewind of the buffer, for every one-tape machine
  whose table agrees with the parser; `Turing.PairParse.cfg_inputSymbol`,
  `cfg_workTapeSymbols`, `cfg_congr`, and the non-writing steps `apply_cfg_stay`,
  `apply_cfg_advance`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.1, the closure properties of p.p.t. machines used implicitly throughout.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–1.3, multi-tape machines and linear-time string
  manipulation.)
-/

/-! ### The buffered aligned parser, shared with the unary-multiplication machine

The parse phase of `pairSplitTM` (below) and of the unary-multiplication machine of
`TCSlib.Complexity.Randomized.Build.UnaryMul`, stated once for every one-tape machine whose table
agrees with the parser at its states: a family `p : Option Bool → S` of parse states (`p none`
expects the first bit of an aligned block, `p (some b)` its second bit after reading `b`), a
rewind state `r` and the state `n` entered after the rewind. -/

namespace Turing.PairParse

/-- The one-buffer configurations of a one-tape machine with states `S`: control `q`, input
head after `i` input bits (at position `i + 1`), the work tape holding the word `a` from the
origin with its head at cell `z`, output `out`. -/
@[simps (config := { isSimp := false }) state inputPos workTapes workTapePos output]
def cfg {S : Type} (x : List Bool) (q : Option S) (i : ℕ) (hi : i ≤ x.length)
    (a : List Bool) (z : ℤ) (out : List Bool) : Cfg 1 Bool S x :=
  ⟨q, ⟨i + 1, by omega⟩, fun _ => FinTM.bufferTape a, fun _ => z, out⟩

/-- At a one-buffer configuration the input head reads the optional entry `x[i]?` (the right
blank when `i = |x|`). -/
theorem cfg_inputSymbol {S : Type} (x : List Bool) (q : Option S) (i : ℕ)
    (hi : i ≤ x.length) (a : List Bool) (z : ℤ) (out : List Bool) :
    (cfg x q i hi a z out).inputSymbol = x[i]? := by
  by_cases h : i < x.length
  · rw [List.getElem?_eq_getElem h]
    exact inputSymbolInner i (by simp [cfg]; omega) h
  · have he : i = x.length := by omega
    subst i
    simp [cfg, Cfg.inputSymbol, Fin.ext_iff]

/-- Two one-buffer configurations with equal input indices are equal (the bound proofs are
irrelevant). -/
theorem cfg_congr {S : Type} (x : List Bool) (q : Option S) {i i' : ℕ}
    (hi : i ≤ x.length) (hi' : i' ≤ x.length) (h : i = i') (a : List Bool) (z : ℤ)
    (out : List Bool) :
    cfg x q i hi a z out = cfg x q i' hi' a z out := by
  subst h
  rfl

/-- At a one-buffer configuration the work head reads cell `z` of the buffer `a`:
`(cfg x q i hi a z out).workTapeSymbols = fun _ => bufferTape a z`. -/
theorem cfg_workTapeSymbols {S : Type} (x : List Bool) (q : Option S) (i : ℕ)
    (hi : i ≤ x.length) (a : List Bool) (z : ℤ) (out : List Bool) :
    (cfg x q i hi a z out).workTapeSymbols = fun _ => FinTM.bufferTape a z :=
  rfl

/-- **A non-writing step that keeps the input head.** The action that writes nothing, keeps the
input head, moves the work head by `d`, emits `o` and enters `q'` maps the one-buffer
configuration `(i, a, z, out)` to the one-buffer configuration `(i, a, z + d, out ++ o)` in
control `q'`. -/
theorem apply_cfg_stay {S : Type} (x : List Bool) (q q' : Option S) (i : ℕ)
    (hi : i ≤ x.length) (a : List Bool) (z : ℤ) (out : List Bool) (d : SignType)
    (o : Option Bool) :
    (⟨0, fun _ => (none, d), o, q'⟩ : Action 1 Bool S).apply (cfg x q i hi a z out) =
      cfg x q' i hi a (z + d) (out ++ o.toList) :=
  Cfg.ext rfl (moveInputPos_zero _) rfl rfl rfl

/-- **A non-writing step that advances the input head.** For `i < |x|`, the action that writes
nothing, moves the input head right, moves the work head by `d`, emits `o` and enters `q'` maps
the one-buffer configuration `(i, a, z, out)` to the one-buffer configuration
`(i + 1, a, z + d, out ++ o)` in control `q'`. -/
theorem apply_cfg_advance {S : Type} (x : List Bool) (q q' : Option S) (i : ℕ)
    (hi : i ≤ x.length) (hi' : i + 1 ≤ x.length) (a : List Bool) (z : ℤ) (out : List Bool)
    (d : SignType) (o : Option Bool) :
    (⟨.pos, fun _ => (none, d), o, q'⟩ : Action 1 Bool S).apply (cfg x q i hi a z out) =
      cfg x q' (i + 1) hi' a (z + d) (out ++ o.toList) :=
  Cfg.ext rfl (moveInputPos_pos_of_ne_right _ (by show i + 1 ≠ x.length + 1; omega)) rfl rfl rfl

/-- **The first half of an aligned block.** For a one-tape machine whose parse state `p none`
reads a bit `b` by moving the input head right into `p (some b)`, silently and without touching
the work tape (`hp0`): at the configuration after the prefix `pre` of `x = pre ++ b :: rest`,
with the buffer `a` and the work head on its right blank, one step reads `b` and enters
`p (some b)`, the buffer and the output unchanged. -/
theorem parse_first {S : Type} (tm : MultiTapeTM 1 Bool S) (p : Option Bool → S)
    (hp0 : ∀ b w, tm.tr (p none) (some b) w = ⟨.pos, fun _ => (none, 0), none, some (p (some b))⟩)
    (x pre rest a : List Bool) (b : Bool) (hx : x = pre ++ b :: rest) :
    tm.step (cfg x (some (p none)) pre.length (by simp [hx]) a a.length []) =
      cfg x (some (p (some b))) (pre.length + 1) (by simp [hx]) a a.length [] := by
  unfold MultiTapeTM.step
  change (tm.tr (p none) _ _).apply _ = _
  rw [cfg_inputSymbol]
  have hr : x[pre.length]? = some b := by simp [hx]
  rw [hr, hp0]
  refine Cfg.ext rfl ?_ rfl ?_ rfl
  · exact moveInputPos_pos_of_ne_right _ (by simp [cfg, hx])
  · funext i; simp [Action.apply, cfg]

/-- **One aligned block.** For a one-tape machine whose parse states act as the buffered aligned
parser (`hp0` as in `parse_first`; `hp1`: at `p (some b)` reading `c`, equal bits append `b` to
the buffer and return to `p none`, the block `10` halts, the block `01` steps the work head back
onto the last stored cell and enters the rewind state `r`, the input head moving right in every
case and nothing emitted): from the configuration after the prefix `pre` of
`x = pre ++ b :: c :: rest`, with the buffer `a` and the work head on its right blank, two steps
read the block and reach, at the input index `|pre| + 2`, the parse state with the buffer
`a ++ [b]` if `b = c`, the halted configuration if `b = true ≠ c`, and the rewind state with the
work head at `|a| - 1` if `b = false ≠ c`; the output stays empty.

**Proof sketch.** The first step is `parse_first`; the second reads `c` at the input index
`|pre| + 1` (`cfg_inputSymbol`). Case analysis on `b` and `c`: equal bits write `b` at the
right blank of the buffer (`Turing.FinTM.bufferTape_append`) and move the work head right, `01`
moves it left into `r`, `10` halts; in every case the input head advances. -/
theorem parse_block {S : Type} (tm : MultiTapeTM 1 Bool S) (p : Option Bool → S) (r : S)
    (hp0 : ∀ b w, tm.tr (p none) (some b) w = ⟨.pos, fun _ => (none, 0), none, some (p (some b))⟩)
    (hp1 : ∀ b c w, tm.tr (p (some b)) (some c) w =
      if b = c then ⟨.pos, fun _ => (some (some b), .pos), none, some (p none)⟩
      else if b then ⟨.pos, fun _ => (none, 0), none, none⟩
      else ⟨.pos, fun _ => (none, .neg), none, some r⟩)
    (x pre rest a : List Bool) (b c : Bool) (hx : x = pre ++ b :: c :: rest) :
    tm.runFrom (cfg x (some (p none)) pre.length (by simp [hx]) a a.length []) 2 =
      if b = c then cfg x (some (p none)) (pre.length + 2) (by simp [hx])
          (a ++ [b]) (a ++ [b]).length []
      else if b then cfg x none (pre.length + 2) (by simp [hx]) a a.length []
      else cfg x (some r) (pre.length + 2) (by simp [hx]) a (a.length - 1) [] := by
  change tm.step (tm.step _) = _
  rw [parse_first tm p hp0 x pre (c :: rest) a b hx]
  unfold MultiTapeTM.step
  change (tm.tr (p (some b)) _ _).apply _ = _
  rw [cfg_inputSymbol]
  have hr : x[pre.length + 1]? = some c := by simp [hx]
  rw [hr, hp1]
  have hm : moveInputPos (⟨pre.length + 1 + 1, by simp [hx]⟩ : Fin (x.length + 2)) .pos =
      ⟨pre.length + 2 + 1, by simp [hx]; omega⟩ :=
    moveInputPos_pos_of_ne_right _ (by simp [hx])
  cases b <;> cases c <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
  all_goals refine Cfg.ext rfl hm ?_ ?_ rfl
  all_goals first
    | rfl
    | (funext i; exact (FinTM.bufferTape_append a _).symm)
    | (funext i; simp [Action.apply, cfg])

/-- **The rewind.** For a one-tape machine whose rewind state `r` moves the work head left while
it reads a stored symbol and, at the left blank, moves it right into the state `n`, the input
head stationary and nothing emitted (`hr`): from the work head at cell `j - 1` of the buffer `a`
(`j ≤ |a|`), `j + 1` steps leave the work head at the origin in the state `n`, the input head
and the output unchanged.

**Proof sketch.** Induction on `j`. At the left blank (`Turing.FinTM.bufferTape_left`) the head
moves right and the state becomes `n`; otherwise the head reads the stored cell
(`Turing.FinTM.bufferTape_nat`), moves left, and the induction hypothesis finishes. -/
theorem rewind_run {S : Type} (tm : MultiTapeTM 1 Bool S) (r n : S)
    (hr : ∀ inp w, tm.tr r inp w = match w 0 with
      | some _ => ⟨0, fun _ => (none, .neg), none, some r⟩
      | none => ⟨0, fun _ => (none, .pos), none, some n⟩)
    (x a : List Bool) (i : ℕ) (hi : i ≤ x.length) (out : List Bool) :
    ∀ j, j ≤ a.length →
    tm.runFrom (cfg x (some r) i hi a ((j : ℤ) - 1) out) (j + 1) = cfg x (some n) i hi a 0 out := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    simp only [hr, cfg, Cfg.workTapeSymbols, Nat.cast_zero, zero_sub, FinTM.bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
    · funext k; simp [Action.apply]
    · simp [Action.apply]
  | succ j ih =>
    intro hj
    have hs : tm.step (cfg x (some r) i hi a (((j + 1 : ℕ) : ℤ) - 1) out) =
        cfg x (some r) i hi a ((j : ℤ) - 1) out := by
      have hz : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [hz]
      unfold MultiTapeTM.step
      simp only [hr, cfg, Cfg.workTapeSymbols, FinTM.bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < a.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
      · funext k; simp [Action.apply, sub_eq_add_neg]
      · simp [Action.apply]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

end Turing.PairParse

namespace Turing

/-- **The unary split** computed by the machine of `Turing.FinTM.exists_pairSplitTM`:
`pairSplitAt ⟨u, b⟩ = ⟨b.take |u|, b.drop |u|⟩`, and `pairSplitAt z = []` when
`pairDecode z = none`. -/
def pairSplitAt (z : List Bool) : List Bool :=
  match pairDecode z with
  | some (u, b) => pairEncode (b.take u.length) (b.drop u.length)
  | none => []

/-- `pairDecode z = some (u, b) → pairSplitAt z = pairEncode (b.take |u|) (b.drop |u|)`. -/
theorem pairSplitAt_of_pairDecode_eq_some {z u b : List Bool} (h : pairDecode z = some (u, b)) :
    pairSplitAt z = pairEncode (b.take u.length) (b.drop u.length) := by
  simp only [pairSplitAt, h]

/-- `pairDecode z = none → pairSplitAt z = []`. -/
theorem pairSplitAt_of_pairDecode_eq_none {z : List Bool} (h : pairDecode z = none) :
    pairSplitAt z = [] := by
  simp only [pairSplitAt, h]

/-- `pairSplitAt ⟨u, b⟩ = ⟨b.take |u|, b.drop |u|⟩`. -/
theorem pairSplitAt_pairEncode (u b : List Bool) :
    pairSplitAt (pairEncode u b) = pairEncode (b.take u.length) (b.drop u.length) :=
  pairSplitAt_of_pairDecode_eq_some (pairDecode_pairEncode u b)

end Turing

namespace Turing.FinTM

/-- Finite control of the coin-splitting machine: `parse none` expects the first bit of an
aligned block and `parse (some b)` its second bit; `rewind` walks the work head back to the
origin; `copy` is the block start of the doubling scan and `dup c` its second emission of
the bit `c`; `sep` emits the second separator bit; `tail` copies the remaining input. -/
private inductive SplitControl where
  | parse (b : Option Bool)
  | rewind
  | copy
  | dup (c : Bool)
  | sep
  | tail

/-- Enumerate the control through a finite sum representation, privately. -/
private instance splitControlFintype : Fintype SplitControl :=
  derive_fintype% _

/-- Compare control states through the same finite sum representation, privately. -/
private instance splitControlDecidableEq : DecidableEq SplitControl :=
  (proxy_equiv% SplitControl).symm.decidableEq

/-- The coin-splitting machine: one work tape holding the undoubled first component. The
parser (`parse`) buffers without emitting and validates the separator; `rewind` returns the
work head to the origin; `copy`/`dup` emit each input bit twice while the work head crosses
the stored first component; `sep` and `tail` emit the separator and the remaining input. -/
private def pairSplitTM : FinTM Bool where
  k := 1
  State := SplitControl
  tm :=
    { q₀ := .parse none
      tr := fun q inp work => match q with
        | .parse none => match inp with
          | some b => ⟨.pos, fun _ => (none, 0), none, some (.parse (some b))⟩
          | none => ⟨0, fun _ => (none, 0), none, none⟩
        | .parse (some b) => match inp with
          | none => ⟨0, fun _ => (none, 0), none, none⟩
          | some c =>
            if b = c then
              ⟨.pos, fun _ => (some (some b), .pos), none, some (.parse none)⟩
            else if b then ⟨.pos, fun _ => (none, 0), none, none⟩
            else ⟨.pos, fun _ => (none, .neg), none, some .rewind⟩
        | .rewind => match work 0 with
          | some _ => ⟨0, fun _ => (none, .neg), none, some .rewind⟩
          | none => ⟨0, fun _ => (none, .pos), none, some .copy⟩
        | .copy => match inp with
          | none => ⟨0, fun _ => (none, 0), some false, some .sep⟩
          | some c =>
            if (work 0).isSome then ⟨0, fun _ => (none, 0), some c, some (.dup c)⟩
            else ⟨0, fun _ => (none, 0), some false, some .sep⟩
        | .dup c => ⟨.pos, fun _ => (none, .pos), some c, some .copy⟩
        | .sep => ⟨0, fun _ => (none, 0), some true, some .tail⟩
        | .tail => match inp with
          | some c => ⟨.pos, fun _ => (none, 0), some c, some .tail⟩
          | none => ⟨0, fun _ => (none, 0), none, none⟩ }

/-- Doubling a word extended by one bit appends the doubled bit. -/
private lemma split_dbl_append (l : List Bool) (c : Bool) :
    dbl (l ++ [c]) = dbl l ++ [c, c] := by
  simp [dbl]

/-- The machine's table at the parse state `parse none`: a bit `b` moves the input head right
into `parse (some b)`, silently (the hypothesis `hp0` of `Turing.PairParse.parse_first`). -/
private lemma split_tr_first (b : Bool) (w : Fin 1 → Option Bool) :
    pairSplitTM.tm.tr (.parse none) (some b) w =
      ⟨.pos, fun _ => (none, 0), none, some (.parse (some b))⟩ :=
  rfl

/-- The machine's table at the parse state `parse (some b)` reading `c`: the aligned-block step
of the parser (the hypothesis `hp1` of `Turing.PairParse.parse_block`, rewind state `rewind`). -/
private lemma split_tr_second (b c : Bool) (w : Fin 1 → Option Bool) :
    pairSplitTM.tm.tr (.parse (some b)) (some c) w =
      if b = c then ⟨.pos, fun _ => (some (some b), .pos), none, some (.parse none)⟩
      else if b then ⟨.pos, fun _ => (none, 0), none, none⟩
      else ⟨.pos, fun _ => (none, .neg), none, some .rewind⟩ :=
  rfl

/-- The machine's table at `rewind`: left over stored symbols, right into `copy` at the left
blank (the hypothesis `hr` of `Turing.PairParse.rewind_run`). -/
private lemma split_tr_rewind (inp : Option Bool) (w : Fin 1 → Option Bool) :
    pairSplitTM.tm.tr .rewind inp w = match w 0 with
      | some _ => ⟨0, fun _ => (none, .neg), none, some .rewind⟩
      | none => ⟨0, fun _ => (none, .pos), none, some .copy⟩ :=
  rfl

/-- The doubling scan: as long as both the stored word and the input have symbols left,
every two steps emit the current input bit twice and advance both heads.
**Proof sketch.** Induct on the number `j` of doubled bits. The `copy` step reads the
stored cell `a[j]` and the input bit `rest[j]`, emits the latter and remembers it in `dup`;
the `dup` step emits it again and moves both heads right. The output after `j` rounds is
`dbl (rest.take j)` (`List.take_succ`). -/
private lemma split_copy (x pre rest a : List Bool) (hx : x = pre ++ rest) :
    ∀ j (_hja : j ≤ a.length) (hjr : j ≤ rest.length),
    pairSplitTM.tm.runFrom (PairParse.cfg x (some .copy) pre.length (by simp [hx]) a 0 [])
        (2 * j) =
      PairParse.cfg x (some .copy) (pre.length + j) (by simp [hx]; omega) a j
        (dbl (rest.take j)) := by
  intro j
  induction j with
  | zero =>
    intro _ _
    rw [Nat.mul_zero, MultiTapeTM.runFrom_zero]
    simp [PairParse.cfg]
  | succ j ih =>
    intro hja hjr
    have hja' : j < a.length := by omega
    have hjr' : j < rest.length := by omega
    have hr : x[pre.length + j]? = some rest[j] := by
      simp [hx, hjr']
    have h1 : pairSplitTM.tm.step
        (PairParse.cfg x (some .copy) (pre.length + j) (by simp [hx]; omega) a j
          (dbl (rest.take j))) =
        PairParse.cfg x (some (.dup rest[j])) (pre.length + j) (by simp [hx]; omega) a j
          (dbl (rest.take j) ++ [rest[j]]) := by
      unfold MultiTapeTM.step
      change (pairSplitTM.tm.tr .copy _ _).apply _ = _
      rw [PairParse.cfg_inputSymbol, hr]
      simp only [pairSplitTM, PairParse.cfg, Cfg.workTapeSymbols, bufferTape_nat,
        List.getElem?_eq_getElem hja', Option.isSome_some, ↓reduceIte]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext k; simp [Action.apply]
    have h2 : pairSplitTM.tm.step
        (PairParse.cfg x (some (.dup rest[j])) (pre.length + j) (by simp [hx]; omega) a j
          (dbl (rest.take j) ++ [rest[j]])) =
        PairParse.cfg x (some .copy) (pre.length + (j + 1)) (by simp [hx]; omega) a
          ((j + 1 : ℕ) : ℤ) (dbl (rest.take (j + 1))) := by
      unfold MultiTapeTM.step
      change (pairSplitTM.tm.tr (.dup rest[j]) _ _).apply _ = _
      refine Cfg.ext rfl ?_ rfl ?_ ?_
      · show moveInputPos (⟨pre.length + j + 1, _⟩ : Fin (x.length + 2)) .pos = _
        rw [moveInputPos_pos_of_ne_right _ (by simp [hx]; omega)]
        simp only [PairParse.cfg, Fin.ext_iff]
        omega
      · funext k; simp [pairSplitTM, Action.apply, PairParse.cfg]
      · show dbl (rest.take j) ++ [rest[j]] ++ (some rest[j]).toList = dbl (rest.take (j + 1))
        rw [List.take_succ, List.getElem?_eq_getElem hjr', Option.toList_some, split_dbl_append]
        simp
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_succ_eq_step', ih (by omega) (by omega), h1, h2]

/-- When the stored word or the input is exhausted, the `copy` state emits the separator
`01` in two steps (`copy` emits `false` and `sep` emits `true`) without moving any head.
**Proof sketch.** First step: if the input is exhausted, `copy` reads the blank and emits
`false`; otherwise the stored word is exhausted, the work head reads the right blank
(`bufferTape_nat`, `isSome none = false`) and the same transition fires. Second step:
`sep` emits `true` unconditionally and enters `tail`. Both steps are stationary. -/
private lemma split_sep (x : List Bool) (i : ℕ) (hi : i ≤ x.length) (a : List Bool) (m : ℕ)
    (out : List Bool) (h : a[m]? = none ∨ x[i]? = none) :
    pairSplitTM.tm.runFrom (PairParse.cfg x (some .copy) i hi a m out) 2 =
      PairParse.cfg x (some .tail) i hi a m (out ++ [false, true]) := by
  have h1 : pairSplitTM.tm.step (PairParse.cfg x (some .copy) i hi a m out) =
      PairParse.cfg x (some .sep) i hi a m (out ++ [false]) := by
    unfold MultiTapeTM.step
    change (pairSplitTM.tm.tr .copy _ _).apply _ = _
    rw [PairParse.cfg_inputSymbol]
    rcases h with h | h
    · cases hxi : x[i]? with
      | none =>
        refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
        funext k; simp [pairSplitTM, Action.apply, PairParse.cfg]
      | some c =>
        simp only [pairSplitTM, PairParse.cfg, Cfg.workTapeSymbols, bufferTape_nat, h,
          Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
        refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
        funext k; simp [Action.apply]
    · rw [h]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext k; simp [pairSplitTM, Action.apply, PairParse.cfg]
  have h2 : pairSplitTM.tm.step (PairParse.cfg x (some .sep) i hi a m (out ++ [false])) =
      PairParse.cfg x (some .tail) i hi a m (out ++ [false, true]) := by
    unfold MultiTapeTM.step
    change (pairSplitTM.tm.tr .sep _ _).apply _ = _
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
    · funext k; simp [pairSplitTM, Action.apply, PairParse.cfg]
    · simp [pairSplitTM, Action.apply, PairParse.cfg]
  change pairSplitTM.tm.step (pairSplitTM.tm.step _) = _
  rw [h1, h2]

/-- The final phase copies the remaining input verbatim and halts at the right blank.
**Proof sketch.** The input prefix grows by one at each emitting transition; the buffer
and its head remain fixed. The right-blank test supplies the final halting step. -/
private lemma split_tail (x rest a : List Bool) (z : ℤ) : ∀ pre out (hx : x = pre ++ rest),
    pairSplitTM.tm.runFrom (PairParse.cfg x (some .tail) pre.length (by simp [hx]) a z out)
        (rest.length + 1) =
      PairParse.cfg x none x.length (le_refl _) a z (out ++ rest) := by
  induction rest with
  | nil =>
    intro pre out hx
    simp only [List.length_nil, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (pairSplitTM.tm.tr .tail _ _).apply _ = _
    rw [PairParse.cfg_inputSymbol]
    have hr : x[pre.length]? = none := by simp [hx]
    rw [hr]
    refine Cfg.ext rfl ?_ rfl ?_ ?_
    · simp [pairSplitTM, Action.apply, PairParse.cfg, hx]
    · funext k; simp [pairSplitTM, Action.apply, PairParse.cfg]
    · simp [pairSplitTM, Action.apply, PairParse.cfg]
  | cons b rest ih =>
    intro pre out hx
    have hs : pairSplitTM.tm.step
        (PairParse.cfg x (some .tail) pre.length (by simp [hx]) a z out) =
        PairParse.cfg x (some .tail) (pre ++ [b]).length (by simp [hx]) a z (out ++ [b]) := by
      unfold MultiTapeTM.step
      change (pairSplitTM.tm.tr .tail _ _).apply _ = _
      rw [PairParse.cfg_inputSymbol]
      have hr : x[pre.length]? = some b := by simp [hx]
      rw [hr]
      refine Cfg.ext rfl ?_ rfl ?_ rfl
      · simpa [PairParse.cfg] using moveInputPos_pos_of_ne_right
          (⟨pre.length + 1, by simp [hx]; omega⟩ : Fin (x.length + 2)) (by simp [hx])
      · funext k; simp [pairSplitTM, Action.apply, PairParse.cfg]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [b]) (out ++ [b]) (by simpa [List.append_assoc] using hx)

/-- Once the separator has been validated, rewind, doubling scan, separator and tail cost
at most `2|a| + |rest| + 4` steps and emit exactly the output pair.
**Proof sketch.** Let `m = min |a| |rest|`. The rewind costs `|a| + 1`
(`Turing.PairParse.rewind_run`), the doubling scan `2m` (`split_copy`), the separator `2`
(`split_sep`; at head `m` the stored word or the input is exhausted) and the tail
`|rest| - m + 1` (`split_tail` after re-indexing the input position past `rest.take m`). The
output is
`dbl (rest.take m) ++ 01 ++ rest.drop m`, and `take`/`drop` at `m` agree with `take`/`drop`
at `|a|` because both saturate. -/
private lemma split_finish (x pre rest a : List Bool) (hx : x = pre ++ rest) :
    ∃ t ≤ 2 * a.length + rest.length + 4,
      (pairSplitTM.tm.runFrom
        (PairParse.cfg x (some .rewind) pre.length (by simp [hx]) a (a.length - 1) []) t).state =
          none ∧
      (pairSplitTM.tm.runFrom
        (PairParse.cfg x (some .rewind) pre.length (by simp [hx]) a (a.length - 1) []) t).output =
          dbl (rest.take a.length) ++ [false, true] ++ rest.drop a.length := by
  obtain ⟨m, hm⟩ : ∃ m, m = min a.length rest.length := ⟨_, rfl⟩
  have hma : m ≤ a.length := hm ▸ Nat.min_le_left _ _
  have hmr : m ≤ rest.length := hm ▸ Nat.min_le_right _ _
  have hcases : m = a.length ∨ (m = rest.length ∧ rest.length ≤ a.length) := by
    rcases Nat.le_total a.length rest.length with h | h
    · exact Or.inl (hm ▸ Nat.min_eq_left h)
    · exact Or.inr ⟨hm ▸ Nat.min_eq_right h, h⟩
  have hsep : a[m]? = none ∨ x[pre.length + m]? = none := by
    rcases hcases with h | ⟨h, _⟩
    · left
      rw [h]
      exact List.getElem?_eq_none (le_refl _)
    · right
      rw [h, hx]
      exact List.getElem?_eq_none (by simp)
  have htake : rest.take m = rest.take a.length := by
    rcases hcases with h | ⟨h, hle⟩
    · rw [h]
    · rw [h, List.take_length, List.take_of_length_le hle]
  have hdrop : rest.drop m = rest.drop a.length := by
    rcases hcases with h | ⟨h, hle⟩
    · rw [h]
    · rw [h, List.drop_length, List.drop_of_length_le hle]
  have hlen : (pre ++ rest.take m).length = pre.length + m := by
    simp [List.length_take, Nat.min_eq_left hmr]
  have hx' : x = (pre ++ rest.take m) ++ rest.drop m := by
    rw [List.append_assoc, List.take_append_drop]
    exact hx
  refine ⟨(a.length + 1) + (2 * m + 2) + ((rest.drop m).length + 1), ?_, ?_⟩
  · simp only [List.length_drop]
    omega
  · rw [MultiTapeTM.runFrom_add _ (a.length + 1 + (2 * m + 2)) ((rest.drop m).length + 1),
      MultiTapeTM.runFrom_add _ (a.length + 1) (2 * m + 2),
      PairParse.rewind_run pairSplitTM.tm .rewind .copy split_tr_rewind x a _ _ [] a.length
        (le_refl _), MultiTapeTM.runFrom_add _ (2 * m) 2,
      split_copy x pre rest a hx m hma hmr, split_sep x _ _ a m _ hsep,
      PairParse.cfg_congr x _ _ (by simp [hx]) hlen.symm,
      split_tail x (rest.drop m) a m (pre ++ rest.take m) _ hx']
    simp [PairParse.cfg, htake, hdrop]

/-- The silent aligned parser either rejects or validates and runs the emission phases.
**Proof sketch.** Induct over aligned two-bit blocks while carrying the already-decoded
buffer. A doubled bit costs two steps and enlarges the buffer by one
(`Turing.PairParse.parse_block`); the linear potential `3|rest| + 2|a| + 5` pays for both effects.
Missing and forbidden separators halt silently with empty output. At `01`, apply the finish
ledger `split_finish`. -/
private lemma split_run (x rest : List Bool) : ∀ pre a (hx : x = pre ++ rest),
    ∃ t ≤ 3 * rest.length + 2 * a.length + 5,
      (pairSplitTM.tm.runFrom
        (PairParse.cfg x (some (.parse none)) pre.length (by simp [hx]) a a.length []) t).state =
          none ∧
      (pairSplitTM.tm.runFrom
        (PairParse.cfg x (some (.parse none)) pre.length (by simp [hx]) a a.length []) t).output =
          match pairDecode rest with
          | some (u, b) => dbl (b.take (a.length + u.length)) ++ [false, true] ++
              b.drop (a.length + u.length)
          | none => [] := by
  induction rest using List.twoStepInduction with
  | nil =>
    intro pre a hx
    refine ⟨1, by omega, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((pairSplitTM.tm.tr (.parse none) _ _).apply _).state = none ∧ _
    rw [PairParse.cfg_inputSymbol]
    simp [hx, pairSplitTM, Action.apply, PairParse.cfg, pairDecode]
  | singleton b =>
    intro pre a hx
    refine ⟨2, by simp, ?_⟩
    change (pairSplitTM.tm.step (pairSplitTM.tm.step _)).state = none ∧
      (pairSplitTM.tm.step (pairSplitTM.tm.step _)).output = _
    rw [PairParse.parse_first pairSplitTM.tm SplitControl.parse split_tr_first x pre [] a b hx]
    unfold MultiTapeTM.step
    change ((pairSplitTM.tm.tr (.parse (some b)) _ _).apply _).state = none ∧ _
    rw [PairParse.cfg_inputSymbol]
    cases b <;> simp [hx, pairSplitTM, Action.apply, PairParse.cfg, pairDecode]
  | cons_cons b c rest ih _ =>
    intro pre a hx
    by_cases h : b = c
    · subst c
      obtain ⟨t, ht, hs, ho⟩ :=
        ih (pre ++ [b, b]) (a ++ [b]) (by simpa [List.append_assoc] using hx)
      refine ⟨2 + t, by
        simp only [List.length_append, List.length_cons, List.length_nil] at *; omega, ?_⟩
      rw [MultiTapeTM.runFrom_add, PairParse.parse_block pairSplitTM.tm SplitControl.parse .rewind
        split_tr_first split_tr_second x pre rest a b b hx, if_pos rfl]
      simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
      refine ⟨?_, ?_⟩
      · simpa only [List.length_append, List.length_cons, List.length_nil] using hs
      · cases hd : pairDecode rest with
        | none => cases b <;> simpa [pairDecode, hd] using ho
        | some p =>
          obtain ⟨u, v⟩ := p
          have e : a.length + (u.length + 1) = a.length + 1 + u.length := by omega
          cases b <;> simpa [pairDecode, hd, e] using ho
    · cases b <;> cases c
      · exact False.elim (h rfl)
      · obtain ⟨t, ht, hs, ho⟩ := split_finish x (pre ++ [false, true]) rest a
          (by simpa [List.append_assoc] using hx)
        refine ⟨2 + t, by simp only [List.length_cons]; omega, ?_⟩
        rw [MultiTapeTM.runFrom_add, PairParse.parse_block pairSplitTM.tm SplitControl.parse
          .rewind split_tr_first split_tr_second x pre rest a false true hx]
        simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
        exact ⟨hs, by simpa [pairDecode] using ho⟩
      · refine ⟨2, by simp, ?_⟩
        rw [PairParse.parse_block pairSplitTM.tm SplitControl.parse .rewind split_tr_first
          split_tr_second x pre rest a true false hx]
        simp [PairParse.cfg, pairDecode]
      · exact False.elim (h rfl)

/-- The coin-splitting machine halts on every input within `5(|x| + 1)` steps with the
output pair `⟨b.take |u|, b.drop |u|⟩` (for `x = ⟨u, b⟩`) or `[]` (malformed `x`). The
initial buffer and decoded prefix are empty.
**Proof sketch.** Instantiate `split_run` with the empty prefix and the empty buffer; the
initial configuration is the indexed configuration at index `0` with blank work tape
(`Cfg.ext`). On a decoded pair the output `dbl (b.take |u|) ++ 01 ++ b.drop |u|` is
`pairEncode (b.take |u|) (b.drop |u|)` by `pairEncode_eq_dbl`; the ledger
`3|x| + 5 ≤ 5(|x| + 1)` is absorbed by `ComputesInTime.mono`. -/
private lemma split_computes (x : List Bool) :
    pairSplitTM.ComputesInTime x
      (match pairDecode x with
        | some (u, b) => pairEncode (b.take u.length) (b.drop u.length)
        | none => []) (5 * (x.length + 1)) := by
  obtain ⟨t, ht, hs, ho⟩ := split_run x x [] [] rfl
  have hinit : pairSplitTM.tm.initCfg x =
      PairParse.cfg x (some (.parse none)) 0 (by omega) [] 0 [] := by
    apply Cfg.ext <;> simp [pairSplitTM, PairParse.cfg, MultiTapeTM.initCfg, Cfg.init]
  have hh : pairSplitTM.ComputesInTime x
      (match pairDecode x with
        | some (u, b) => pairEncode (b.take u.length) (b.drop u.length)
        | none => []) t := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [hinit]
    refine ⟨hs, ?_⟩
    cases hd : pairDecode x with
    | none => simpa [hd] using ho
    | some p =>
      obtain ⟨u, b⟩ := p
      simpa [hd, pairEncode_eq_dbl] using ho
  exact hh.mono (by simp only [List.length_nil] at ht; omega)

/-- **The coin-splitting machine exists:** a finite machine computes, on a pair `⟨u, b⟩`,
the pair `⟨b.take |u|, b.drop |u|⟩` — and `[]` on a malformed word — within `5 (n + 1)`
steps on inputs of length `n`. This is the machine behind
`Turing.FinTM.computesFunInTime_pairSplitAt` [PS10, §2.1, implicit; inventory Claim-26.3(c)].

**Proof sketch.** The private machine `pairSplitTM` above (one work tape, six control
modes: buffered aligned parser, rewind, doubling scan, separator, tail) with the step
ledger `split_run`: `3 |x| + 5 ≤ 5 (|x| + 1)` steps from the initial configuration, output
`dbl (b.take |u|) ++ 01 ++ b.drop |u| = pairEncode (b.take |u|) (b.drop |u|)`
(`Turing.pairEncode_eq_dbl`). -/
theorem exists_pairSplitTM :
    ∃ M : FinTM Bool,
      M.ComputesFunInTime pairSplitAt fun n => 5 * (n + 1) :=
  ⟨pairSplitTM, (computesFunInTime_iff _ _ _).2 fun x => split_computes x⟩

end Turing.FinTM

## ===== TCSlib/Complexity/Randomized/Primitives.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Build.PairSplit
import TCSlib.Complexity.Randomized.Build.UnaryMul
import TCSlib.Complexity.Randomized.PolyExpr

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Two new machine primitives: coin splitting and unary multiplication

The closure calculus of non-uniform PPTs ([PS10, §2.1], implicit in every reduction of
chapters 2–4; inventory item Claim-26.3) needs two string machines that the library's
catalog `TCSlib.Complexity.TuringMachine.Build.Primitives` does not provide:

* `Turing.FinTM.computesFunInTime_pairSplitAt` — `⟨u, b⟩ ↦ ⟨b.take |u|, b.drop |u|⟩`: cut a
  coin string at a unary length (fresh coin segments as independent uniform strings);
* `Turing.FinTM.computesFunInTime_unaryMul` — `⟨1^a, 1^b⟩ ↦ 1^{ab}`: unary multiplication,
  which makes every syntactic polynomial computable in unary
  (`Complexity.polyTimeComputable_unaryPoly`) without the repetition lemma (D9).

Both are built in the `Build/` style (foundation decision D11): explicit finite machines with
a proved timed contract (`TCSlib.Complexity.Randomized.Build.PairSplit`,
`TCSlib.Complexity.Randomized.Build.UnaryMul`). This file states the two contracts with their
construction sketches (DESIGN.md §2.4) and derives the FP-level consequences the closure
catalogue consumes:
`polyTimeComputable_unaryPoly` (by induction on the expression, the `mul` case being the
only use of `unaryMul`) and the typed cuts `polyTimeComputable_pairTakePoly` /
`polyTimeComputable_pairDropPoly` (`pairSplitAt` applied to `⟨1^{p(|fst z|)}, snd z⟩`).

The unary evaluator is hosted here rather than in `TCSlib.Complexity.Randomized.PolyExpr`
because its `mul` case needs `unaryMul`, while the cuts below need both the evaluator and
`PolyExpr`; this keeps the import graph acyclic.

## Main results

* `Turing.FinTM.computesFunInTime_pairSplitAt` — coin splitting at a unary length, linear
  time (proved; the machine is `Turing.FinTM.exists_pairSplitTM` in
  `TCSlib.Complexity.Randomized.Build.PairSplit`).
* `Turing.FinTM.computesFunInTime_unaryMul` — unary multiplication, quadratic time
  (proved; the machine is `Turing.FinTM.exists_unaryMulTM` in
  `TCSlib.Complexity.Randomized.Build.UnaryMul`).
* `Complexity.polyTimeComputable_unaryPoly` — `x ↦ 1^{p(|x|)}` is polynomial-time
  computable for every syntactic polynomial `p` (proved by induction; the `mul` and `pow`
  cases rest on `unaryMul`).
* `Complexity.polyTimeComputable_pairTakePoly`, `Complexity.polyTimeComputable_pairDropPoly`
  — on `⟨u, b⟩`, the first / the remaining `p(|u|)` bits of `b` (proved from `pairSplitAt`).

## Main definitions

None (the primitives are existence statements over `Turing.FinTM Bool`). The split function
`Turing.pairSplitAt` and its readers live in `TCSlib.Complexity.Randomized.Build.PairSplit`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.1, the closure properties of p.p.t. machines used implicitly throughout.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–1.3, multi-tape machines and linear-time string
  manipulation.)
-/

namespace Turing.FinTM

/-- **Coin splitting at a unary length** (new primitive): on a pair `⟨u, b⟩` the machine
outputs the pair `⟨b.take |u|, b.drop |u|⟩`; on a malformed word it outputs `[]`. Linear
time. This is how a reduction uses disjoint segments of its coin string as independent
uniform strings [PS10, §2.1, implicit; inventory Claim-26.3(c)].

**Proof sketch (construction, DESIGN.md §2.4; built in
`TCSlib.Complexity.Randomized.Build.PairSplit`).** One work tape. Phase 1 is the buffered
aligned parser of `Turing.FinTM.computesFunInTime_pairFst`: it reads the doubled prefix of
`u` onto the work tape without emitting anything, and stops at the separator `01` (a
malformed prefix halts with empty output). Phase 2 rewinds the work head. Phase 3 is a copy
scan of `b`: while the work head walks across the stored `u`, each bit `c` of `b` read on
the input tape is emitted doubled as `cc` (the doubled first component of the output pair);
when the stored `u` is exhausted the machine emits the separator `01` and then copies the
remainder of `b` verbatim (if `b` is shorter than `u`, the separator is emitted when the
input ends and the second component is empty). The step ledger gives at most `5 (n + 1)`
steps; the output is `pairEncode (b.take |u|) (b.drop |u|)` by `Turing.pairEncode_eq_dbl`
(`Turing.FinTM.exists_pairSplitTM`, with `c = 5`). -/
theorem computesFunInTime_pairSplitAt :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime pairSplitAt fun n => c * (n + 1) := by
  obtain ⟨M, hM⟩ := exists_pairSplitTM
  exact ⟨M, 5, hM⟩

/-- **Unary multiplication** (new primitive): on a pair `⟨u, v⟩` the machine outputs
`1^{|u| · |v|}`; on a malformed word it outputs `[]`. Quadratic time. With it every syntactic
polynomial is computable in unary (`Complexity.polyTimeComputable_unaryPoly`), so the lengths
`1^{p(n)}` that reductions need never go through the repetition lemma (D9).

**Proof sketch (construction, DESIGN.md §2.4; built in
`TCSlib.Complexity.Randomized.Build.UnaryMul`).** One work tape. Phase 1 is the buffered
aligned parser of `Turing.FinTM.computesFunInTime_pairFst`: it undoubles the prefix `u` onto
the work tape without emitting anything (one cell per token of `u`, so the content of `u` is
irrelevant) and validates the separator `01`; a malformed input halts with empty output.
Phase 2 rewinds the work head and then, for each symbol of the second component `v` (read
left to right, its content irrelevant), walks across the stored word emitting one `true`
per cell (`emitAction`-style) and rewinds the work tape; at the end of the input it halts.
**Deviation from the DESIGN.md sketch** (which stores `v` and replays it once per token of
`u`): storing `u` and replaying it once per symbol of `v` needs no input rewind, and the
product `|u| · |v|` is the same. The run takes `|u| + 1 + |v| (2 |u| + 3) + 1` steps after
the parser, at most `(n + 1) ^ 2 + 3 n + 5 ≤ 5 (n + 1) ^ 2` in all (step ledger `mul_run`),
and the output is `List.replicate (|u| * |v|) true` by induction on the symbols of `v`
(`List.replicate_add`, `Nat.mul_succ`) — `Turing.FinTM.exists_unaryMulTM`, with `c = 5`. -/
theorem computesFunInTime_unaryMul :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun z => match pairDecode z with
          | some (u, v) => List.replicate (u.length * v.length) true
          | none => [])
        fun n => c * (n + 1) ^ 2 := by
  obtain ⟨M, hM⟩ := exists_unaryMulTM
  exact ⟨M, 5, hM⟩

end Turing.FinTM

namespace Complexity

open Turing

/-- FP-level unary multiplication: if `x ↦ 1^{f x}` and `x ↦ 1^{g x}` are polynomial-time
computable, so is `x ↦ 1^{f x · g x}` (pair the two unary strings with
`PolyTimeComputable.pairEncode` and apply the unary-multiplication machine). -/
private theorem polyTimeComputable_unaryMulFun {f g : List Bool → ℕ}
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

/-- **The unary evaluator of a syntactic polynomial is polynomial-time:** for every
`p : PolyExpr`, the map `x ↦ 1^{p(|x|)}` is polynomial-time computable. This is the device by
which a reduction produces every length `1^{p(n)}` it needs (coin cuts, parameter changes,
padding), foundation decision D9; it is never routed through the repetition lemma.

**Proof sketch.** Induction on `p`. `const c`: the constant string `1^c`
(`Complexity.polyTimeComputable_const`). `var`: `x ↦ 1^{|x|}`
(`Complexity.polyTimeComputable_unary`). `add p q`: concatenate the two unary strings
(`Complexity.PolyTimeComputable.append`, `List.replicate_add`). `mul p q`: pair the two unary
strings and apply the unary-multiplication machine `Turing.FinTM.computesFunInTime_unaryMul`
(the only case that uses the new primitive). `pow p c`: inner induction on `c`, the step
being the `mul` case against `1^{p(|x|)}` (`pow_succ`). -/
theorem polyTimeComputable_unaryPoly (p : PolyExpr) :
    PolyTimeComputable fun x => List.replicate (p.eval x.length) true := by
  induction p with
  | const c => exact polyTimeComputable_const (List.replicate c true)
  | var => exact polyTimeComputable_unary
  | add p q hp hq =>
    simpa only [PolyExpr.eval_add, List.replicate_add] using hp.append hq
  | mul p q hp hq => exact polyTimeComputable_unaryMulFun hp hq
  | pow p c hp =>
    induction c with
    | zero => simpa using polyTimeComputable_const (List.replicate 1 true)
    | succ c ih =>
      simpa only [PolyExpr.eval_pow, pow_succ] using polyTimeComputable_unaryMulFun ih hp

/-- The FP form of the coin-splitting machine: `z ↦ ⟨(snd z).take |fst z|, (snd z).drop |fst z|⟩`
on pairs, `[]` on malformed words. -/
private theorem polyTimeComputable_pairSplitAt : PolyTimeComputable pairSplitAt := by
  obtain ⟨M, c, hM⟩ := Turing.FinTM.computesFunInTime_pairSplitAt
  exact polyTimeComputable_of_linear ⟨M, c, hM⟩

/-- The re-pairing `z ↦ ⟨1^{p(|fst z|)}, snd z⟩` is polynomial-time (the unary evaluator on
the first component, paired with the second component). -/
private theorem polyTimeComputable_pairUnaryFst (p : PolyExpr) :
    PolyTimeComputable fun z =>
      pairEncode (List.replicate (p.eval (pairFstD z).length) true) (pairSndD z) :=
  ((polyTimeComputable_unaryPoly p).comp polyTimeComputable_pairFstD).pairEncode
    polyTimeComputable_pairSndD

/-- **Typed coin cut, head:** on `z = ⟨u, b⟩`, the first `p(|u|)` bits of `b` are
polynomial-time computable (`z ↦ (snd z).take (p(|fst z|))`, with the total projections
`Complexity.pairFstD`/`pairSndD`). A reduction run on `⟨1^n, r⟩` thereby reads the first
`p(n)` coins as data [PS10, §2.1, implicit; inventory Claim-26.3(c)].

**Proof sketch.** `pairFstD ∘ pairSplitAt ∘ (z ↦ ⟨1^{p(|fst z|)}, snd z⟩)`: the re-pairing is
`polyTimeComputable_unaryPoly p` on `pairFstD` paired with `pairSndD`
(`PolyTimeComputable.pairEncode`), the split is `Turing.FinTM.computesFunInTime_pairSplitAt`
via `polyTimeComputable_of_linear`, and the composite equals the claimed function by
`Turing.pairSplitAt_pairEncode`, `Complexity.pairFstD_pairEncode` and `List.length_replicate`
(`PolyTimeComputable.comp`, `funext`). -/
theorem polyTimeComputable_pairTakePoly (p : PolyExpr) :
    PolyTimeComputable fun z => (pairSndD z).take (p.eval (pairFstD z).length) := by
  convert polyTimeComputable_pairFstD.comp
    (polyTimeComputable_pairSplitAt.comp (polyTimeComputable_pairUnaryFst p)) using 1
  funext z
  simp [pairSplitAt_pairEncode]

/-- **Typed coin cut, tail:** on `z = ⟨u, b⟩`, the bits of `b` after the first `p(|u|)` are
polynomial-time computable (`z ↦ (snd z).drop (p(|fst z|))`): the remaining coins of a
reduction after the first `p(n)` were consumed.

**Proof sketch.** As `polyTimeComputable_pairTakePoly` with `pairSndD` in place of `pairFstD`
after the split (`Complexity.pairSndD_pairEncode`). -/
theorem polyTimeComputable_pairDropPoly (p : PolyExpr) :
    PolyTimeComputable fun z => (pairSndD z).drop (p.eval (pairFstD z).length) := by
  convert polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairSplitAt.comp (polyTimeComputable_pairUnaryFst p)) using 1
  funext z
  simp [pairSplitAt_pairEncode]

end Complexity

## ===== TCSlib/Complexity/Randomized/UnaryPolynomial.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.TuringMachine.Build.WordTiming
import TCSlib.Complexity.Randomized.PolyExpr
import Mathlib.Algebra.Polynomial.Eval.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Unary polynomial evaluation with an output-length time bound

For each fixed syntactic polynomial, a multitape machine emits its value at one plus the input length. Its time is proportional to the input and output lengths. Expanding into nonzero monomials allows the sharp monomial machines to be combined without an extra power of the input length.

## Main definitions

The private polynomial translation connects syntactic expressions to polynomials over the natural numbers.

## Main results

* `Complexity.exists_unaryPoly_succ_computesFunInTime` computes the unary value within the combined input and output length.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010. (§2.13, Lemma 64.3.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2, multitape machines, and §7.2, efficient arithmetic.)
-/

open Turing
open scoped BigOperators

attribute [local irreducible] FinTM.ComputesFunInTime FinTM.ComputesInTime

namespace Complexity

open Turing.FinTM

/-- The ordinary polynomial denoted by the syntactic arithmetic expression. -/
private noncomputable def toNatPolynomial : PolyExpr → Polynomial ℕ
  | .const a => Polynomial.C a
  | .var => Polynomial.X
  | .add p q => toNatPolynomial p + toNatPolynomial q
  | .mul p q => toNatPolynomial p * toNatPolynomial q
  | .pow p e => toNatPolynomial p ^ e

/-- The polynomial agrees with the syntactic evaluator.

**Proof sketch.** Induct over the expression using the polynomial evaluation laws. -/
private theorem toNatPolynomial_eval (p : PolyExpr) (n : ℕ) :
    (toNatPolynomial p).eval n = p.eval n := by
  induction p <;> simp_all only [toNatPolynomial, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, PolyExpr.eval_const,
    PolyExpr.eval_var, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_pow]

/-- Nonzero monomials can be evaluated and concatenated at a cost proportional
to their total output length plus the input length.

**Proof sketch.** Induct over the finite set of exponents. The sharp monomial
emitter charges a constant multiple of the monomial, since its coefficient is
positive. Use the bounded concatenation theorem for that emitter and the tail. -/
private theorem exists_unaryMonomialSum (coeff : ℕ → ℕ) (s : Finset ℕ)
    (hs : ∀ e ∈ s, 0 < coeff e) :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime
      (fun x => List.replicate (∑ e ∈ s, coeff e * (x.length + 1) ^ e) true)
      (fun n => c * ((∑ e ∈ s, coeff e * (n + 1) ^ e) + n + 1)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨constTM [], 1, (computesFunInTime_iff _ _ _).2 fun x => ?_⟩
    simp only [Finset.sum_empty, List.replicate_zero, Nat.zero_add, Nat.one_mul]
    exact (constTM_computes [] x).mono (by simp)
  | @insert e s he ih =>
    have hpos := hs e (Finset.mem_insert_self _ _)
    obtain ⟨G, b, hG⟩ := ih (fun i hi => hs i (Finset.mem_insert_of_mem hi))
    let a := coeff e + 5 * e + 4
    obtain ⟨M, c, hM⟩ := exists_append_computesFunInTime (polyUnaryTM_computes (coeff e) e) hG
    refine ⟨M, c * (a + b + 1), (computesFunInTime_iff _ _ _).2 fun x => ?_⟩
    rw [Finset.sum_insert he, List.replicate_add]
    let n := x.length
    let term := coeff e * (n + 1) ^ e
    let rest := ∑ i ∈ s, coeff i * (n + 1) ^ i
    let total := term + rest + n + 1
    have hpow : (n + 1) ^ e ≤ term := by
      simpa only [Nat.one_mul] using
        Nat.mul_le_mul_right ((n + 1) ^ e) hpos
    have hterm : (n + 1) ^ e ≤ total := hpow.trans (by dsimp only [total]; omega)
    have hrest : rest + n + 1 ≤ total := by dsimp only [total]; omega
    have hn : n + 1 ≤ total := by dsimp only [total]; omega
    refine ((computesFunInTime_iff _ _ _).1 hM x).mono ?_
    change c * (a * (n + 1) ^ e + b * (rest + n + 1) + n + 1) ≤
      c * (a + b + 1) * total
    calc
      _ ≤ c * (a * total + b * total + total) := by
        apply Nat.mul_le_mul_left
        simpa only [Nat.add_assoc] using
          Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hterm)
            (Nat.mul_le_mul_left _ hrest)) hn
      _ = _ := by ring

/-- The unary value of a syntactic polynomial at one plus the input length is
computable in time proportional to the sum of the input and output lengths.

**Proof sketch.** Expand the polynomial into its nonzero monomials. For each
degree use the sharp monomial emitter, and concatenate their unary outputs. -/
theorem exists_unaryPoly_succ_computesFunInTime (p : PolyExpr) :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime
      (fun x => List.replicate (p.eval (x.length + 1)) true)
      (fun n => c * (p.eval (n + 1) + n + 1)) := by
  let P := toNatPolynomial p
  have heval (n : ℕ) : p.eval n = ∑ e ∈ P.support, P.coeff e * n ^ e := by
    rw [← toNatPolynomial_eval, ← show P = toNatPolynomial p from rfl,
      Polynomial.eval_eq_sum, Polynomial.sum_def]
  obtain ⟨M, c, hM⟩ := exists_unaryMonomialSum P.coeff P.support fun e he =>
    Nat.pos_of_ne_zero (Polynomial.mem_support_iff.1 he)
  refine ⟨M, c, (computesFunInTime_iff _ _ _).2 fun x => ?_⟩
  rw [heval]
  exact (computesFunInTime_iff _ _ _).1 hM x

end Complexity

## ===== TCSlib/Complexity/TuringMachine.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Configuration
import TCSlib.Complexity.TuringMachine.Deterministic
import TCSlib.Complexity.TuringMachine.StateRenaming
import TCSlib.Complexity.TuringMachine.Finite
import TCSlib.Complexity.TuringMachine.Nondeterministic
import TCSlib.Complexity.TuringMachine.NondeterministicSpace
import TCSlib.Complexity.TuringMachine.ChoiceReplay
import TCSlib.Complexity.TuringMachine.Oracle
import TCSlib.Complexity.TuringMachine.OracleFinite
import TCSlib.Complexity.TuringMachine.OracleNondeterministic
import TCSlib.Complexity.TuringMachine.OracleAgreement
import TCSlib.Complexity.TuringMachine.Simulation
import TCSlib.Complexity.TuringMachine.BufferWords
import TCSlib.Complexity.TuringMachine.Sweep
import TCSlib.Complexity.TuringMachine.Composition
import TCSlib.Complexity.TuringMachine.UnaryTape
import TCSlib.Complexity.TuringMachine.CounterProg
import TCSlib.Complexity.TuringMachine.CounterProgRun
import TCSlib.Complexity.TuringMachine.CounterProgInput
import TCSlib.Complexity.TuringMachine.Build.Convention
import TCSlib.Complexity.TuringMachine.Build.Wrappers
import TCSlib.Complexity.TuringMachine.Build.Loop
import TCSlib.Complexity.TuringMachine.Build.Primitives
import TCSlib.Complexity.TuringMachine.Build.WordTiming
import TCSlib.Complexity.TuringMachine.Build.WordTests
import TCSlib.Complexity.TuringMachine.Build.Embed
import TCSlib.Complexity.TuringMachine.Build.Seam
import TCSlib.Complexity.TuringMachine.Build.NDHost
import TCSlib.Complexity.TuringMachine.Build.VirtualInput
import TCSlib.Complexity.TuringMachine.Build.Zone
import TCSlib.Complexity.TuringMachine.Build.ZoneTape
import TCSlib.Complexity.TuringMachine.Build.ZoneRebalance
import TCSlib.Complexity.TuringMachine.Build.Catalog
import TCSlib.Complexity.TuringMachine.Build.OracleCall
import TCSlib.Complexity.TuringMachine.SymbolLift
import TCSlib.Complexity.TuringMachine.Build.CounterLoop
import TCSlib.Complexity.TuringMachine.Build.InputWindow
import TCSlib.Complexity.TuringMachine.Build.SeamLayout
import TCSlib.Complexity.TuringMachine.Build.Rewind
import TCSlib.Complexity.TuringMachine.Build.InputRewind
import TCSlib.Complexity.TuringMachine.Build.InterpreterStartup
import TCSlib.Complexity.TuringMachine.Build.Scan
import TCSlib.Complexity.TuringMachine.Build.InputCall
import TCSlib.Complexity.TuringMachine.Build.CfgRecord
import TCSlib.Complexity.TuringMachine.Build.InputLength
import TCSlib.Complexity.TuringMachine.Build.RecordTable
import TCSlib.Complexity.TuringMachine.Build.CertShell
import TCSlib.Complexity.TuringMachine.Build.OracleSim
import TCSlib.Complexity.TuringMachine.Build.Contract
import TCSlib.Complexity.TuringMachine.Build.NDCombinators
import TCSlib.Complexity.TuringMachine.Build.NDClockHost
import TCSlib.Complexity.TuringMachine.Build.NDClockHostRun
import TCSlib.Complexity.TuringMachine.Build.StepClock
import TCSlib.Complexity.TuringMachine.Build.WindowRun
import TCSlib.Complexity.TuringMachine.Build.InputDevice
import TCSlib.Complexity.TuringMachine.Build.StepBlock
import TCSlib.Complexity.TuringMachine.Build.StepBlockLoop
import TCSlib.Complexity.TuringMachine.Build.StepBlockForward
import TCSlib.Complexity.TuringMachine.Build.ModuleHost
import TCSlib.Complexity.TuringMachine.CodeSimulator
import TCSlib.Complexity.TuringMachine.ChoiceWords
import TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction
import TCSlib.Complexity.TuringMachine.Robustness.SingleTape
import TCSlib.Complexity.TuringMachine.Robustness.Bidirectional
import TCSlib.Complexity.TuringMachine.Robustness.ObliviousSchedule
import TCSlib.Complexity.TuringMachine.Robustness.ObliviousCandidate
import TCSlib.Complexity.TuringMachine.Robustness.ObliviousSetup
import TCSlib.Complexity.TuringMachine.Robustness.ObliviousLedger
import TCSlib.Complexity.TuringMachine.Robustness.Oblivious
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.TuringMachine.CodeParser
import TCSlib.Complexity.TuringMachine.CodeFormat
import TCSlib.Complexity.TuringMachine.Codes2Tape
import TCSlib.Complexity.TuringMachine.MathlibBridge
import TCSlib.Complexity.TuringMachine.UniversalStartup
import TCSlib.Complexity.TuringMachine.UniversalK
import TCSlib.Complexity.TuringMachine.SelfUniversal
import TCSlib.Complexity.TuringMachine.UniversalInterpreter
import TCSlib.Complexity.TuringMachine.UniversalBlock
import TCSlib.Complexity.TuringMachine.Universal
import TCSlib.Complexity.TuringMachine.NDCodes
import TCSlib.Complexity.TuringMachine.NDCodeSimulator

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Complexity — Turing machines

The multi-tape Turing machine model underlying the Arora-Barak formalization
(see `AroraBarakChapter1Plan.md`): a machine-free configuration/action layer, the
deterministic machine with time and space semantics, the bundled finite layer over which
all complexity classes are stated, and oracle machines as a wrapper over the same
configurations.

The core model files are vendored from cslib
(https://github.com/leanprover/cslib, commit a3747758, 2026-09-14); see the file headers
for the local modifications.

## Contents

* `CodeFormat` — shared transition-record and table-format parsers, with the one-tape instance.
* `Codes2Tape` — the deterministic two-work-tape code scheme (§13, Z3), an instance of
  `CodeFormat`, with its uniform scheme from `CodeSimulator`.

* `Configuration` — configurations `Cfg`, actions `Action` and their application; the
  space measure. Nothing here mentions a machine (vendored).
* `Deterministic` — `MultiTapeTM`, the step/run semantics, time and space bounds
  (vendored).
* `StateRenaming` — transport of actions, configurations, and machines along maps
  of the state type; shared by the oracle embedding and the code normal form.
* `Finite` — the bundled `FinTM` layer carrying `Fintype`/`DecidableEq` state instances;
  all headline definitions are stated over it.
* `Nondeterministic` — binary-choice nondeterministic machines [AB09, §2.1.2]:
  choice-word run semantics, all-branch halting, the bundled `FinNDTM` layer, the
  deterministic embedding, and the run-level transfer, slice, relabelling and input-locality
  lemmas (the classes live in `ClassNP/NTIME`).
* `NondeterministicSpace` — the space measure of binary-choice NDTMs along choice-word
  runs: visited cells, as for the deterministic `SPACE` [AB09, Definition 4.1].
* `ChoiceReplay` — choice-tape determinization: the replay machine of an NDTM, which reads its
  choices from an extra work tape, and the replay lemma [AB09, §2.1.2, Theorem 2.6]. Proved.
* `Oracle` — oracle machines `OracleTM` [AB09, §3.4]: same configurations, oracle-dependent
  step; the embedding of plain machines and its oracle-independence sanity theorems.
* `OracleFinite` — the bundled finite layer `FinOracleTM`, carrying well-formedness as a
  field, over which the oracle classes are stated [AB09, Definition 3.5].
* `OracleNondeterministic` — nondeterministic oracle machines [AB09, Definition 3.4], for
  `NPOracle` and the relativization theorem.
* `OracleAgreement` — oracle locality: runs under oracles agreeing on every submitted
  string coincide [AB09, Theorem 3.7].
* `NDCodes` — codes for nondeterministic machines [AB09, §1.4, §3.2]: the two-work-tape
  coded normal form, its fixed serialization, and the scheme laws with the effective
  (canonizer) form.
* `NDCodeSimulator` — the interpreter core for nondeterministic codes (C1): the serialization
  bridge, the per-code replay canonizer and the core `R` [AB09, Exercise 2.6]. The core is
  proved; the canonizer is sorried.
* `Simulation` — generic machine-construction gadgets: emission chains, control
  actions, disjoint tape-block embeddings with lockstep run lemmas, the input-head
  rewind, and the two-machine branch union.
* `BufferWords` — the cells of a buffer tape holding a composite word: a suffix at an offset, a
  middle word's letters, prefixes and suffixes, the blank cells off the word, and a unary word
  with its terminator. Proved.
* `Sweep` — the generic zipper/transduction layer for sweep-based tape
  simulations, with the initialized-run head/support bound.
* `Composition` — identity/constant machines and closure of time-bounded computability
  under composition; also the formal home of the append-only-output convention
  argument.
* `UnaryTape` — work tapes holding a number in unary.
* `CounterProg`, `CounterProgRun` — counter programs (goto programs over unary registers)
  compiled into machines, with Hoare-style run lemmas; the model of the polynomial-time
  emitters of [AB09, Remark 6.7] (polynomial time: `ClassNP/CounterProgPolyTime`).
* `Build/Embed`, `Build/Seam`, `Build/Catalog` — the §12 routine layer
  (`machine-library-design.md` §12, gate closed round 3): the bank-embedding
  transformers with their returning flavors, seam composition with the
  general-configuration forms and the release adapter, and the space-annotated
  catalog rows.
* `Build/NDHost` — the nondeterministic phase host over NDTM phases and the choice writer, for
  the guess-first route of the nondeterministic time hierarchy (C1). Proved, the writer's
  bounded contract included (C1-W, 2026-10-17).
* `Build/VirtualInput` — virtual-input hosting (`machine-library-design.md` §13, Z1): a
  machine whose input is a buffered work-tape word runs inside a host, one step per step.
* `Build/Zone` — the pure zone layer (§13, Z2, as revised by §13d): zone contents, the
  guarded pairwise ops, the cascade and its mirror, the scanned index, the total rebalance,
  the extension by one level, and the virtual tape a track represents.
* `Build/ZoneTape` — the multi-track zoned carrier over `ZoneSym k` (§13d, G3): the layout
  with blank separators, the inner-packed encoding `zonedTape` and its invariants.
* `Build/ZoneRebalance` — the rebalance and extension rows (§13d, G4), as contracts.
  Proved.
* `Build/OracleCall` — the oracle-machine rows (`machine-library-design.md` §12.9):
  W1 capture onto the query tape, landing in `qQuery`, and the two-step answer tail.
* `SymbolLift` — the embedding transport (`machine-library-design.md` §12.8, R8.0): a
  `Bool` machine run on a richer alphabet along `e : Bool ↪ Γ`, with time and space
  unchanged.
* `Build/CounterLoop` — the counter-driven loop (§12.7) and the pattern expansion
  `expandTM` (§12.8, R8.6).
* `Build/InputWindow` — the counter-driven copy of a bounded window of the native input onto a
  work tape, for the nondeterministic time hierarchy [AB09, Theorem 3.2]. Proved.
* `Build/SeamLayout` — the step block's table and summary tapes from a captured serialization,
  the one redistribution the step-block startups cite. Proved.
* `Build/Rewind` — the rewind of a work-tape head to the start of a word, from any cell of the
  word or just past it, the empty word included. Proved.
* `Build/InputRewind` — the rewind of the native input head to the first input cell: its exact
  time, its first arrival at the park, and its unchanged work tapes, heads and output; and the
  composition of two state relabelings of a configuration. Proved.
* `Build/InterpreterStartup` — the pieces of a universal machine's startup on a timed paired
  input: the header projections and their capture, the suffix window, the released install call,
  the table-and-summary layout, the seam step, a fresh capture's start. Proved.
* `Build/Scan`, `Build/InputCall`, `Build/CfgRecord` — the §12.8 rows, with the field
  layout, compare, seeks and two-pass scan in `Build/Catalog`'s Part 3: the constant and
  advancing writers and the native-input copy and fold; the input call and input seek;
  the rich configuration-record carrier and the record rows. All proved (§12.8 fill gate
  closed).
* `Build/InputLength`, `Build/RecordTable` — the deferred §12.8 rows (`machine-library-design.md`
  §12.8b): the input length `Nat.bits |x|` (R8.5c), and the table layer over records (header,
  sentinels, find, append, template, init, validity, odometer next, the end-to-start adapter).
  Fills in progress; each module's header carries its status.
* `Build/OracleSim`, `Build/CertShell` — oracle-call simulation (§12.10, the B1b extension): one
  plain host simulating an oracle machine with queries answered by a plain decider, the
  choice-word machine of an oracle NDTM, and the plain certificate shell. Fills in progress;
  each module's header carries its status.
* `Build/StepBlock` — the step block (host H2, `machine-library-design.md` §14): one finite
  machine per work-tape count `k` that performs one simulated transition of a `k`-tape
  binary table held as data, with its contract `Turing.StepBlock.roundTM_effect`, the
  record skipper and fixed-field reader, the per-round space ledger and the cofinal
  iteration. Proved; promoted from `CodeSimulator` (H2-S gate closed, round 2).
* `Build/StepBlockLoop` — the step block's counter loop (host H2's loop form, H2-L,
  `machine-library-design.md` §14): the binary deadline clock over the step block, native and on
  a buffered input, from any represented live start, with its early-escape bound and live
  exits. Proved; harvested from `CodeSimulator` (H1 harvest gate passed, 2026-10-14).
* `Build/StepBlockForward` — the step block's forwarding round loop (host H2's unclocked loop form,
  H2-F, `machine-library-design.md` §14): any `k`-tape table simulated in macro-step lockstep with
  its emissions forwarded, per-step cost bounded by the table's length, and a space ledger.
  Statement gate passed 2026-10-15; the contract is sorried.
* `Build/ModuleHost` — the clean-module host (host H14, `machine-library-design.md` §14): the
  first-halting clean-module contract `Turing.ModuleHost.Clean` with the install and emit modules
  of every polynomial-time word function, and the finite host running such modules over a
  shared tape bank with consumer-supplied control states (`host_call`, `host_clean`). Proved;
  harvested 2026-11-05 from `ClassNP/SAT`'s private module layer and its copy in
  `Randomized/Build/IterateFindHost` (gate 03l, R-03l-1).
* `CodeSimulator` — the format-parameterized uniform simulator over item 8's code formats
  (B5a): one bounded-acceptance interpreter and canonizer whose one- and two-tape instances are
  the EXPCOM and Codes2Tape code schemes. Fills in progress; the module header carries its
  status.
* `ChoiceWords` — certificate and choice words: split uniqueness for length-determined
  suffixes, the exact NP certificate length's monotonicity, the choice budget, and the
  truncation of halted branch runs. Shared by the plain Theorem 2.6, the oracle simulation's
  choice-word law and the certificate shell (wave-1 statement gate, round 1).
* `CounterProgInput` — transport a counter-program run past an input prefix
  that has already been consumed.
* `Build/Contract` — the framed-contract library (MIG-0a and MIG-0b, `machine-library-design.md`
  §16a), the facade of `Build/Contract/{Basic,Seam,Embed,Catalog,Lift}`: exact time, an endpoint
  function, an exit set with a no-earlier-exit cut and head envelopes, a derived frames layer,
  the compositions `trans`, `seq`, `inPhase`, `embed`, `branch` and the releases as thin
  wrappers over the public rows, and the segment, round and joint-trajectory layers with state
  renaming and the macro-step lockstep. The core, `Build/Contract/Basic`, imports only the
  machine core. Proved; the MIG-0a and MIG-0b gates closed.
* `Build/NDCombinators`, `Build/NDClockHost`, `Build/NDClockHostRun` — the nondeterministic
  construction rows: run locality, output maps and the coin dispatcher for binary-choice
  machines, and the clocked restart host `Turing.FinNDTM.clockHost` (clocked runner and
  restart loop of [AB09, §7.4.2, Exercise 7.6(a)]) with its startup and round contracts.
* `Build/StepClock`, `Build/WindowRun` — host H3 (`machine-library-design.md` §14): the
  step-clocked runner, shared with the nondeterministic time hierarchy; the semantic windowed
  run `windowRun`; the windowed round loop and the step-clocked windowed runner. Statement gate
  passed 2026-10-14; the specification is proved, the machine contracts are sorried.
* `Build/InputDevice` — host H5: the input-device interface, the native device, and the
  bounded-prefix ruler device with its boundary test, call rows and host. Proved.
* `Build/Convention`, `Build/Wrappers`, `Build/Loop`, `Build/Primitives` — the
  machine-construction library (`machine-library-design.md`): the `Cfg.ofWords` seam
  discipline, the capture/silence and halt-redirect wrappers with the timed branch,
  the bounded-loop combinator, and the primitive catalog of timed string functions.
  Proved, and audited at the shared-infrastructure gates.
* `Build/WordTiming` — concatenation of computed words with an additive time bound.
* `Build/WordTests` — two linear-time one-bit word tests, equality with a fixed word and the
  all-`true` word, in the form the timed conditional takes as its test. Proved.
* `Robustness/AlphabetReduction` — binary alphabet suffices [AB09, Claim 1.5].
* `Robustness/SingleTape` — one work tape suffices, quadratically [AB09, Claim 1.6].
* `Robustness/Bidirectional` — unidirectional tape use suffices [AB09, Claim 1.8].
* `Robustness/Oblivious` — oblivious machines and the quadratic oblivious simulation
  [AB09, Remark 1.7, Exercise 1.5] (imports the `ClassP` definitions it needs).
* `Encoding` — machines as strings [AB09, §1.4]: the code normal form `CodeTM`, the
  fixed canonical serialization, the representation-scheme laws `MachineCode`, and
  the effective scheme `EffectiveMachineCode` that the universal machine requires.
* `Universal` — the universal machine [AB09, Theorem 1.9]: the all-string evaluator
  with linear overhead and divergence preservation, the relaxed quadratic
  total-function form, and the time-bounded variant (code-first input layout).
* `UniversalK` — the `k`-generic universal machine (U2) [AB09, Theorem 1.9]: the `k`-tape
  scheme interface `EffectiveCodeK` with the one- and two-tape schemes as instances, the startup,
  the self-application universal machine with time and space ledgers, and the code-first
  evaluator, all proved.
* `SelfUniversal` — the self-application universal machine `U₀` and its startup
  [AB09, Exercise 4.1], the universal machine of the space hierarchy's window route.
  Both are proved, as the `k = 1` cases of `UniversalK`'s statements.
-/

## ===== TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean =====

/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.TuringMachine.Build.EmitIterEmbed

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The emit-iteration body

The host machine behind `Complexity.polyTimeComputable_emitIter` (in
`TCSlib.Complexity.ClassNP.PolyTimeBlockLoop`): one finite machine that, on
input `w`, concatenates the chunks `e (g^[i] w)` for `i = 0, …, R |w|`, in
polynomial time, given machines for the step `g` and the chunk `e` and a
polynomial length envelope for the orbit of `g`.

It is an instance of `Turing.FinTM.exists_emitLoopTM`.  The body machine's
startup copies the native input onto work tape zero (the loop's round state)
and rewinds both heads to the canonical seam; each round is two clean calls
on the tape-resident state word — an emit-mode call
(`Turing.FinTM.exists_emitCallTM`) forwarding the chunk `e s` to the physical
output, then an install-mode call (`Turing.FinTM.exists_installCallTM`)
replacing the word by `g s` — glued by two control states.  The clean-call
modules run on the body's first tapes through a tape-padding, state-injecting
embedding (`padAction`/`embedCfg` below); the round assembly commutes the
already-emitted chunk past the install call with an output-prefix lemma.

## Main definitions

None — the body machine, its embedding, and the phase configurations are
private to this file.

## Main results

* `Turing.FinTM.exists_emitIterTM_withFuel` — emitting iteration with a supplied fuel machine and a separate round-count bound.
* `Turing.FinTM.exists_emitIterTM` — the finite machine computing the
  concatenated chunks of a polynomially clocked iteration, within a
  polynomial budget in the `C·(n+1)^c` normal form.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2; §7.3–§7.4: the folklore
  "simulate the machine on each block" loop this host implements.)
-/


namespace Turing

open MultiTapeTM

variable {k m : ℕ} {B SS : Type} {x : List Bool}

/-! ### The body machine

Startup copies the native input onto work tape zero and rewinds both heads;
a round is the emit-mode call (whose first action the anchor itself performs,
so an entry state equal to the exit state still runs), a control handoff, the
install-mode call (likewise inlined into `gStart`), and a control return to
the anchor. -/

/-- Control states of the emit-iteration body. -/
private inductive BodyState (SE SG : Type) where
  | copy
  | rwTape
  | rwInput0
  | rwInput
  | anchor
  | callE (q : SE)
  | gStart
  | callG (q : SG)
  deriving DecidableEq

private instance {SE SG : Type} [Fintype SE] [Fintype SG] :
    Fintype (BodyState SE SG) := derive_fintype% _

/-- The emit-iteration body: copy the input onto tape zero, then alternate
the two clean-call modules under the anchored round discipline. -/
private def emitIterBody (Em Gm : FinTM Bool) (hek : 0 < Em.k)
    (ee ex : Em.State) (ge gx : Gm.State) : FinTM Bool where
  k := max Em.k Gm.k
  State := BodyState Em.State Gm.State
  tm := {
    q₀ := .copy
    tr := fun q inp work => match q with
      | .copy => match inp with
        | some s => ⟨.pos,
            fun i => if (i : ℕ) = 0 then (some (some s), 1) else (none, 0),
            none, some .copy⟩
        | none => ⟨0,
            fun i => if (i : ℕ) = 0 then (none, -1) else (none, 0),
            none, some .rwTape⟩
      | .rwTape =>
        match work ⟨0, Nat.lt_of_lt_of_le hek (Nat.le_max_left _ _)⟩ with
        | some _ => ⟨0,
            fun i => if (i : ℕ) = 0 then (none, -1) else (none, 0),
            none, some .rwTape⟩
        | none => ⟨0,
            fun i => if (i : ℕ) = 0 then (none, 1) else (none, 0),
            none, some .rwInput0⟩
      | .rwInput0 => FinTM.controlAction .neg (some .rwInput)
      | .rwInput => match inp with
        | some _ => FinTM.controlAction .neg (some .rwInput)
        | none => FinTM.controlAction .pos (some .anchor)
      | .anchor =>
        padAction (Nat.le_max_left _ _) (Option.map .callE)
          (Em.tm.tr ee inp (fun i => work (Fin.castLE (Nat.le_max_left _ _) i)))
      | .callE q =>
        if q = ex then FinTM.controlAction 0 (some .gStart)
        else
          padAction (Nat.le_max_left _ _) (Option.map .callE)
            (Em.tm.tr q inp (fun i => work (Fin.castLE (Nat.le_max_left _ _) i)))
      | .gStart =>
        padAction (Nat.le_max_right _ _) (Option.map .callG)
          (Gm.tm.tr ge inp (fun i => work (Fin.castLE (Nat.le_max_right _ _) i)))
      | .callG q =>
        if q = gx then FinTM.controlAction 0 (some .anchor)
        else
          padAction (Nat.le_max_right _ _) (Option.map .callG)
            (Gm.tm.tr q inp (fun i => work (Fin.castLE (Nat.le_max_right _ _) i))) }

/-- A pure control transition replaces only the state. -/
private theorem control_step {H : MultiTapeTM k Bool B} {q r : B}
    (h : ∀ inp work, H.tr q inp work = FinTM.controlAction 0 (some r))
    {c : Cfg k Bool B x} (hc : c.state = some q) :
    H.step c = { c with state := some r } := by
  have hs : H.step c = (H.tr q c.inputSymbol c.workTapeSymbols).apply c := by
    unfold MultiTapeTM.step
    rw [hc]
  rw [hs, h]
  refine Cfg.ext rfl ?_ ?_ ?_ ?_ <;>
    simp [FinTM.controlAction, Action.apply]

/-- A moving control transition replaces the state and moves the input head. -/
private theorem control_step' {H : MultiTapeTM k Bool B} {q r : B} {mv : SignType}
    (h : ∀ inp work, H.tr q inp work = FinTM.controlAction mv (some r))
    {c : Cfg k Bool B x} (hc : c.state = some q) :
    H.step c = { c with
      state := some r
      inputPos := moveInputPos c.inputPos mv } := by
  have hs : H.step c = (H.tr q c.inputSymbol c.workTapeSymbols).apply c := by
    unfold MultiTapeTM.step
    rw [hc]
  rw [hs, h]
  refine Cfg.ext rfl rfl ?_ ?_ ?_ <;>
    simp [FinTM.controlAction, Action.apply]

section Body

variable (Em Gm : FinTM Bool) (ee ex : Em.State) (ge gx : Gm.State)

/-- Embedding an `Em`-seam into the body gives a body seam: tape zero's word
survives and the padding tapes are blank on both sides. -/
private theorem embed_ofWords_left (hek : 0 < Em.k) (s : List Bool) :
    embedCfg (Nat.le_max_left Em.k Gm.k) (BodyState.callE (SG := Gm.State))
        (Cfg.ofWords (input := x) ee (stateWord Em.k s)) =
      Cfg.ofWords (BodyState.callE ee) (stateWord (max Em.k Gm.k) s) := by
  rw [embedCfg_ofWords]
  congr 1
  funext i
  by_cases h : (i : ℕ) < Em.k
  · simp [stateWord, h]
  · have h0 : ¬ (i : ℕ) = 0 := fun hz => h (hz ▸ hek)
    simp [stateWord, h, h0]

/-- Embedding a `Gm`-seam into the body gives a body seam, provided `Gm` has
a genuine tape (otherwise tape zero's word would be lost). -/
private theorem embed_ofWords_right (hgk : 0 < Gm.k) (s : List Bool) :
    embedCfg (Nat.le_max_right Em.k Gm.k) (BodyState.callG (SE := Em.State))
        (Cfg.ofWords (input := x) ge (stateWord Gm.k s)) =
      Cfg.ofWords (BodyState.callG ge) (stateWord (max Em.k Gm.k) s) := by
  rw [embedCfg_ofWords]
  congr 1
  funext i
  by_cases h : (i : ℕ) < Gm.k
  · simp [stateWord, h]
  · have h0 : ¬ (i : ℕ) = 0 := fun hz => h (hz ▸ hgk)
    simp [stateWord, h, h0]

/-- **The round segment.** From the anchor seam carrying `s`, the body runs
the emit-mode module (emitting `es`), hands control to the install-mode
module (installing `gs`), and returns to the anchor seam, in positive time,
without visiting the anchor strictly inside.
**Proof sketch.** The anchor itself fires the emit module's first action, so
an entry state equal to the exit state still runs; `embed_run` transports the
rest of the emit run, landing at the handoff state with the chunk emitted and
the word preserved.  One control step enters `gStart`, which fires the
install module's first action; the install run is transported likewise, with
the already-emitted chunk commuted past it by `runFrom_output_prefix` (the
install module's own output stays empty along the run, by the append-only
output).  One final control step re-enters the anchor carrying the stepped
word.  The anchor-exclusion clause reads the visited state off the
appropriate phase equality: an injected call state, or a control state,
never the anchor. -/
private theorem body_round (hek : 0 < Em.k) (hgk : 0 < Gm.k) (s es gs : List Bool)
    (tE : ℕ) (htE : 0 < tE)
    (hEfirst : ∀ t', 0 < t' → t' < tE →
      (Em.tm.runFrom (Cfg.ofWords (input := x) ee (stateWord Em.k s)) t').state ≠
        some ex)
    (hErun : Em.tm.runFrom (Cfg.ofWords (input := x) ee (stateWord Em.k s)) tE =
      { Cfg.ofWords ex (stateWord Em.k s) with output := es })
    (tG : ℕ) (htG : 0 < tG)
    (hGfirst : ∀ t', 0 < t' → t' < tG →
      (Gm.tm.runFrom (Cfg.ofWords (input := x) ge (stateWord Gm.k s)) t').state ≠
        some gx)
    (hGrun : Gm.tm.runFrom (Cfg.ofWords (input := x) ge (stateWord Gm.k s)) tG =
      Cfg.ofWords gx (stateWord Gm.k gs)) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.runFrom
        (Cfg.ofWords (input := x) .anchor (stateWord (max Em.k Gm.k) s))
        (tE + 1 + tG + 1) =
      { Cfg.ofWords (input := x) .anchor (stateWord (max Em.k Gm.k) gs)
          with output := es } ∧
    ∀ t', 0 < t' → t' < tE + 1 + tG + 1 →
      ((emitIterBody Em Gm hek ee ex ge gx).tm.runFrom
        (Cfg.ofWords (input := x) .anchor (stateWord (max Em.k Gm.k) s))
          t').state ≠ some .anchor := by
  set H := (emitIterBody Em Gm hek ee ex ge gx).tm with hH
  set c₀ : Cfg (max Em.k Gm.k) Bool (BodyState Em.State Gm.State) x :=
    Cfg.ofWords .anchor (stateWord (max Em.k Gm.k) s) with hc₀
  set subc₀ : Cfg Em.k Bool Em.State x := Cfg.ofWords ee (stateWord Em.k s) with hsubc₀
  set subg₀ : Cfg Gm.k Bool Gm.State x := Cfg.ofWords ge (stateWord Gm.k s) with hsubg₀
  have htrE : ∀ q : Em.State, q ≠ ex → ∀ inp work,
      H.tr (.callE q) inp work =
        padAction (Nat.le_max_left Em.k Gm.k) (Option.map .callE)
          (Em.tm.tr q inp (fun i => work (Fin.castLE (Nat.le_max_left _ _) i))) := by
    intro q hq inp work
    simp [hH, emitIterBody, hq]
  have htrG : ∀ q : Gm.State, q ≠ gx → ∀ inp work,
      H.tr (.callG q) inp work =
        padAction (Nat.le_max_right Em.k Gm.k) (Option.map .callG)
          (Gm.tm.tr q inp (fun i => work (Fin.castLE (Nat.le_max_right _ _) i))) := by
    intro q hq inp work
    simp [hH, emitIterBody, hq]
  -- the first module step, fired from the anchor
  have hstep₁ : H.step c₀ =
      embedCfg (Nat.le_max_left Em.k Gm.k) (BodyState.callE (SG := Gm.State))
        (Em.tm.step subc₀) := by
    have h := embed_step (Nat.le_max_left Em.k Gm.k) Em.tm H
      (BodyState.callE (SG := Gm.State)) subc₀ ee rfl .anchor (fun inp work => rfl)
    have hcfg : ({ embedCfg (Nat.le_max_left Em.k Gm.k)
        (BodyState.callE (SG := Gm.State)) subc₀ with
        state := some .anchor } : Cfg (max Em.k Gm.k) Bool _ x) = c₀ := by
      rw [hsubc₀, embed_ofWords_left Em Gm ee hek]
      rfl
    rw [← hcfg]
    exact h
  -- the module chain after the first step
  have hEsome : ∀ j ≤ tE, ∃ q, (Em.tm.runFrom subc₀ j).state = some q := by
    intro j hj
    exact state_isSome_of_runFrom Em.tm (by rw [hErun]; rfl) hj
  have hone : Em.tm.runFrom subc₀ 1 = Em.tm.step subc₀ := by
    simp [MultiTapeTM.runFrom]
  have hEchain : ∀ u ≤ tE - 1,
      H.runFrom c₀ (1 + u) =
        embedCfg (Nat.le_max_left Em.k Gm.k) (BodyState.callE (SG := Gm.State))
          (Em.tm.runFrom subc₀ (1 + u)) := by
    intro u hu
    rw [runFrom_add, runFrom_one, hstep₁]
    rw [embed_run (Nat.le_max_left Em.k Gm.k) Em.tm H
      (BodyState.callE (SG := Gm.State)) ex htrE (Em.tm.step subc₀) u ?hstates]
    · rw [runFrom_add, hone]
    case hstates =>
      intro j hj
      have hj1 : 1 + j ≤ tE := by omega
      obtain ⟨q, hq⟩ := hEsome (1 + j) hj1
      rw [runFrom_add, hone] at hq
      refine ⟨q, hq, ?_⟩
      intro hqex
      subst hqex
      have := hEfirst (1 + j) (by omega) (by omega)
      rw [runFrom_add, hone] at this
      exact this hq
  -- checkpoint A: after tE steps, at the handoff state with the chunk emitted
  have hA : H.runFrom c₀ tE =
      { Cfg.ofWords (BodyState.callE ex) (stateWord (max Em.k Gm.k) s)
          with output := es } := by
    have h := hEchain (tE - 1) le_rfl
    rw [show 1 + (tE - 1) = tE from by omega] at h
    rw [h, hErun]
    rw [embedCfg_output, embed_ofWords_left Em Gm ex hek]
  -- checkpoint B: the control handoff
  have hB : H.runFrom c₀ (tE + 1) =
      { Cfg.ofWords BodyState.gStart (stateWord (max Em.k Gm.k) s)
          with output := es } := by
    rw [runFrom_add, hA, runFrom_one, control_step (q := BodyState.callE ex) ?_ rfl]
    · rfl
    · intro inp work
      simp [hH, emitIterBody]
  -- the install chain, lifted along the emitted prefix
  have hstep₂ : H.step (Cfg.ofWords (BodyState.gStart (SE := Em.State) (SG := Gm.State))
        (stateWord (max Em.k Gm.k) s)) =
      embedCfg (Nat.le_max_right Em.k Gm.k) (BodyState.callG (SE := Em.State))
        (Gm.tm.step subg₀) := by
    have h := embed_step (Nat.le_max_right Em.k Gm.k) Gm.tm H
      (BodyState.callG (SE := Em.State)) subg₀ ge rfl
      (BodyState.gStart (SE := Em.State) (SG := Gm.State)) (fun inp work => rfl)
    have hcfg : ({ embedCfg (Nat.le_max_right Em.k Gm.k)
        (BodyState.callG (SE := Em.State)) subg₀ with
        state := some (BodyState.gStart (SE := Em.State) (SG := Gm.State)) } :
          Cfg (max Em.k Gm.k) Bool (BodyState Em.State Gm.State) x) =
        Cfg.ofWords BodyState.gStart (stateWord (max Em.k Gm.k) s) := by
      rw [hsubg₀, embed_ofWords_right Em Gm ge hgk]
      rfl
    rw [← hcfg]
    exact h
  have hGsome : ∀ j ≤ tG, ∃ q, (Gm.tm.runFrom subg₀ j).state = some q := by
    intro j hj
    exact state_isSome_of_runFrom Gm.tm (by rw [hGrun]; rfl) hj
  have honeG : Gm.tm.runFrom subg₀ 1 = Gm.tm.step subg₀ := by
    simp [MultiTapeTM.runFrom]
  have hGchain : ∀ u ≤ tG - 1,
      H.runFrom (Cfg.ofWords (BodyState.gStart (SE := Em.State) (SG := Gm.State)) (stateWord (max Em.k Gm.k) s)) (1 + u) =
        embedCfg (Nat.le_max_right Em.k Gm.k) (BodyState.callG (SE := Em.State))
          (Gm.tm.runFrom subg₀ (1 + u)) := by
    intro u hu
    rw [runFrom_add, runFrom_one, hstep₂]
    rw [embed_run (Nat.le_max_right Em.k Gm.k) Gm.tm H
      (BodyState.callG (SE := Em.State)) gx htrG (Gm.tm.step subg₀) u ?hstatesG]
    · rw [runFrom_add, honeG]
    case hstatesG =>
      intro j hj
      have hj1 : 1 + j ≤ tG := by omega
      obtain ⟨q, hq⟩ := hGsome (1 + j) hj1
      rw [runFrom_add, honeG] at hq
      refine ⟨q, hq, ?_⟩
      intro hqex
      subst hqex
      have := hGfirst (1 + j) (by omega) (by omega)
      rw [runFrom_add, honeG] at this
      exact this hq
  have hGout : ∀ u ≤ tG, 1 ≤ u →
      H.runFrom c₀ (tE + 1 + u) =
        { embedCfg (Nat.le_max_right Em.k Gm.k) (BodyState.callG (SE := Em.State))
            (Gm.tm.runFrom subg₀ u) with output := es } := by
    intro u hu h1u
    rw [show tE + 1 + u = (tE + 1) + u from rfl, runFrom_add, hB]
    have hpre : ({ Cfg.ofWords BodyState.gStart (stateWord (max Em.k Gm.k) s)
        with output := es } : Cfg (max Em.k Gm.k) Bool (BodyState Em.State Gm.State) x) =
        { (Cfg.ofWords BodyState.gStart (stateWord (max Em.k Gm.k) s) :
            Cfg (max Em.k Gm.k) Bool (BodyState Em.State Gm.State) x) with
          output := es ++ (Cfg.ofWords (input := x)
            (BodyState.gStart (SE := Em.State) (SG := Gm.State))
            (stateWord (max Em.k Gm.k) s)).output } := by
      simp [Cfg.ofWords]
    have hsubout : (Gm.tm.runFrom subg₀ u).output = [] := by
      obtain ⟨o2, h2⟩ := runFrom_output_extends Gm.tm (Gm.tm.runFrom subg₀ u) (tG - u)
      rw [← runFrom_add, show u + (tG - u) = tG from by omega, hGrun] at h2
      have : ([] : List Bool) = (Gm.tm.runFrom subg₀ u).output ++ o2 := h2
      exact (List.append_eq_nil_iff.mp this.symm).1
    rw [hpre, runFrom_output_prefix]
    obtain ⟨u', rfl⟩ : ∃ u', u = 1 + u' := ⟨u - 1, by omega⟩
    rw [hGchain u' (by omega)]
    rw [show (embedCfg (Nat.le_max_right Em.k Gm.k) (BodyState.callG (SE := Em.State))
      (Gm.tm.runFrom subg₀ (1 + u'))).output = [] from hsubout, List.append_nil]
  -- checkpoint C and the final control return
  have hC : H.runFrom c₀ (tE + 1 + tG) =
      { Cfg.ofWords (BodyState.callG gx) (stateWord (max Em.k Gm.k) gs)
          with output := es } := by
    rw [hGout tG le_rfl (by omega), hGrun, embed_ofWords_right Em Gm gx hgk]
  constructor
  · rw [show tE + 1 + tG + 1 = (tE + 1 + tG) + 1 from rfl, runFrom_add, hC,
      runFrom_one, control_step (q := BodyState.callG gx) ?_ rfl]
    · rfl
    · intro inp work
      simp [hH, emitIterBody]
  · intro t' ht'0 ht'
    rcases lt_trichotomy t' (tE + 1) with hlt | heq | hgt
    · rcases Nat.lt_or_ge t' tE with hltE | hgeE
      · obtain ⟨u, rfl⟩ : ∃ u, t' = 1 + u := ⟨t' - 1, by omega⟩
        rw [hEchain u (by omega)]
        obtain ⟨q, hq⟩ := hEsome (1 + u) (by omega)
        simp [embedCfg, hq]
      · have he : t' = tE := by omega
        subst he
        rw [hA]
        simp [Cfg.ofWords]
    · subst heq
      rw [hB]
      simp [Cfg.ofWords]
    · obtain ⟨u, rfl⟩ : ∃ u, t' = tE + 1 + u := ⟨t' - (tE + 1), by omega⟩
      rw [hGout u (by omega) (by omega)]
      obtain ⟨q, hq⟩ := hGsome u (by omega)
      simp [embedCfg, hq]

/-! #### The startup copier -/

/-- The copy-phase configuration: the first `i` input symbols already written
on tape zero, both heads past them. -/
private def copyCfg (x : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    Cfg (max Em.k Gm.k) Bool (BodyState Em.State Gm.State) x :=
  ⟨some .copy, ⟨i + 1, by omega⟩,
    fun j => if (j : ℕ) = 0 then FinTM.bufferTape (x.take i) else fun _ => none,
    fun j => if (j : ℕ) = 0 then (i : ℤ) else 0, []⟩

/-- A rewind-phase configuration: the whole input on tape zero, the input
head at `p`, the tape-zero head at `z`. -/
private def fullCfg (x : List Bool) (st : BodyState Em.State Gm.State)
    (p : ℕ) (hp : p < x.length + 2) (z : ℤ) :
    Cfg (max Em.k Gm.k) Bool (BodyState Em.State Gm.State) x :=
  ⟨some st, ⟨p, hp⟩,
    fun j => if (j : ℕ) = 0 then FinTM.bufferTape x else fun _ => none,
    fun j => if (j : ℕ) = 0 then z else 0, []⟩

/-- The body's initial configuration is the empty copy configuration. -/
private theorem initCfg_eq_copyCfg (hek : 0 < Em.k) (x : List Bool) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.initCfg x =
      copyCfg Em Gm x 0 (Nat.zero_le _) := by
  refine Cfg.ext rfl (Fin.ext (by simp [copyCfg])) ?_ ?_ rfl
  · funext j
    by_cases hj : (j : ℕ) = 0 <;>
      simp [copyCfg, emitIterBody, hj, MultiTapeTM.initCfg, Cfg.init]
  · funext j
    by_cases hj : (j : ℕ) = 0 <;>
      simp [copyCfg, emitIterBody, hj, MultiTapeTM.initCfg, Cfg.init]

/-- One copy step: read the next input symbol, write it, advance both heads.
**Proof sketch.** The input symbol under the head is the `i`-th input bit;
the applied action writes it at tape-zero cell `i` (`bufferTape_append`
extends the copied prefix) and moves both heads right. -/
private theorem copy_step (hek : 0 < Em.k) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.step (copyCfg Em Gm x i (le_of_lt hi)) =
      copyCfg Em Gm x (i + 1) hi := by
  have hinp : (copyCfg Em Gm x i (le_of_lt hi)).inputSymbol = some x[i] :=
    inputSymbolInner i (by simp only [copyCfg]; omega) hi
  have h1 : (emitIterBody Em Gm hek ee ex ge gx).tm.step (copyCfg Em Gm x i (le_of_lt hi)) =
      ((emitIterBody Em Gm hek ee ex ge gx).tm.tr .copy
        (copyCfg Em Gm x i (le_of_lt hi)).inputSymbol
        (copyCfg Em Gm x i (le_of_lt hi)).workTapeSymbols).apply
        (copyCfg Em Gm x i (le_of_lt hi)) := rfl
  rw [h1, hinp]
  have htake : x.take (i + 1) = x.take i ++ [x[i]] := by
    rw [List.take_succ, List.getElem?_eq_getElem hi]
    rfl
  have hlen : ((x.take i).length : ℤ) = (i : ℤ) := by
    simp [List.length_take, Nat.min_eq_left (le_of_lt hi)]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · show moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos = _
    rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
    rfl
  · funext j
    by_cases hj : (j : ℕ) = 0
    · simp only [emitIterBody, Action.apply, copyCfg, hj, if_pos]
      rw [htake, FinTM.bufferTape_append, hlen]
    · simp [emitIterBody, Action.apply, copyCfg, hj]
  · funext j
    by_cases hj : (j : ℕ) = 0
    · simp only [emitIterBody, Action.apply, copyCfg, hj, if_pos]
      simp only [SignType.coe_one]
      omega
    · simp [emitIterBody, Action.apply, copyCfg, hj]

/-- The copy phase ends at the right input boundary and starts the tape
rewind.
**Proof sketch.** At the right boundary the input read is blank, so the
copy state's other branch fires: the input head stays, tape zero (now
holding the whole input, `List.take_length`) steps left. -/
private theorem copy_end (hek : 0 < Em.k) (x : List Bool) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.step (copyCfg Em Gm x x.length le_rfl) =
      fullCfg Em Gm x .rwTape (x.length + 1) (by omega) ((x.length : ℤ) - 1) := by
  have hinp : (copyCfg Em Gm x x.length le_rfl).inputSymbol = none := by
    have h := FinTM.inputSymbol_at (copyCfg Em Gm x x.length le_rfl) x.length le_rfl
      (by simp [copyCfg])
    simpa using h
  have h1 : (emitIterBody Em Gm hek ee ex ge gx).tm.step (copyCfg Em Gm x x.length le_rfl) =
      ((emitIterBody Em Gm hek ee ex ge gx).tm.tr .copy
        (copyCfg Em Gm x x.length le_rfl).inputSymbol
        (copyCfg Em Gm x x.length le_rfl).workTapeSymbols).apply
        (copyCfg Em Gm x x.length le_rfl) := rfl
  rw [h1, hinp]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · show moveInputPos (⟨x.length + 1, by omega⟩ : Fin (x.length + 2)) 0 = _
    rw [moveInputPos_zero]
    rfl
  · funext j
    by_cases hj : (j : ℕ) = 0
    · simp only [emitIterBody, Action.apply, copyCfg, fullCfg, hj, if_pos]
      rw [List.take_length]
    · simp [emitIterBody, Action.apply, copyCfg, fullCfg, hj]
  · funext j
    by_cases hj : (j : ℕ) = 0
    · simp only [emitIterBody, Action.apply, copyCfg, fullCfg, hj, if_pos,
        SignType.neg_eq_neg_one, SignType.coe_neg_one]
      omega
    · simp [emitIterBody, Action.apply, copyCfg, fullCfg, hj]

/-- One tape-rewind step over a written cell.
**Proof sketch.** The tape-zero read at cell `j` is the `j`-th copied bit,
so the rewind state keeps moving left; only the head position changes. -/
private theorem rwTape_some (hek : 0 < Em.k) (x : List Bool) (j : ℕ) (hj : j < x.length) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.step
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)) =
      fullCfg Em Gm x .rwTape (x.length + 1) (by omega) ((j : ℤ) - 1) := by
  have hw : (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)).workTapeSymbols
      ⟨0, Nat.lt_of_lt_of_le hek (Nat.le_max_left Em.k Gm.k)⟩ = some x[j] := by
    simp only [fullCfg, Cfg.workTapeSymbols]
    simp [List.getElem?_eq_getElem hj]
  have h1 : (emitIterBody Em Gm hek ee ex ge gx).tm.step
      (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)) =
      ((emitIterBody Em Gm hek ee ex ge gx).tm.tr .rwTape
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)).inputSymbol
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)).workTapeSymbols).apply
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)) := rfl
  have htr : (emitIterBody Em Gm hek ee ex ge gx).tm.tr .rwTape
      (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)).inputSymbol
      (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)).workTapeSymbols =
      ⟨0, fun i => if (i : ℕ) = 0 then (none, -1) else (none, 0), none, some .rwTape⟩ := by
    simp only [emitIterBody]
    rw [hw]
  rw [h1, htr]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · show moveInputPos (⟨x.length + 1, by omega⟩ : Fin (x.length + 2)) 0 = _
    rw [moveInputPos_zero]
    rfl
  · funext i
    by_cases hi : (i : ℕ) = 0 <;> simp [Action.apply, fullCfg, hi]
  · funext i
    by_cases hi : (i : ℕ) = 0
    · simp only [Action.apply, fullCfg, hi, if_pos, SignType.neg_eq_neg_one,
        SignType.coe_neg_one]
      omega
    · simp [Action.apply, fullCfg, hi]

/-- The tape rewind reaches the left blank and turns the head back to the
origin.
**Proof sketch.** Cell `-1` is blank (`bufferTape_left`), so the rewind
state's blank branch fires: the head steps right to the origin and control
moves to the input rewind. -/
private theorem rwTape_none (hek : 0 < Em.k) (x : List Bool) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.step
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)) =
      fullCfg Em Gm x .rwInput0 (x.length + 1) (by omega) 0 := by
  have hw : (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)).workTapeSymbols
      ⟨0, Nat.lt_of_lt_of_le hek (Nat.le_max_left Em.k Gm.k)⟩ = none := by
    simp only [fullCfg, Cfg.workTapeSymbols]
    simp
  have h1 : (emitIterBody Em Gm hek ee ex ge gx).tm.step
      (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)) =
      ((emitIterBody Em Gm hek ee ex ge gx).tm.tr .rwTape
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)).inputSymbol
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)).workTapeSymbols).apply
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)) := rfl
  have htr : (emitIterBody Em Gm hek ee ex ge gx).tm.tr .rwTape
      (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)).inputSymbol
      (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)).workTapeSymbols =
      ⟨0, fun i => if (i : ℕ) = 0 then (none, 1) else (none, 0), none, some .rwInput0⟩ := by
    simp only [emitIterBody]
    rw [hw]
  rw [h1, htr]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · show moveInputPos (⟨x.length + 1, by omega⟩ : Fin (x.length + 2)) 0 = _
    rw [moveInputPos_zero]
    rfl
  · funext i
    by_cases hi : (i : ℕ) = 0 <;> simp [Action.apply, fullCfg, hi]
  · funext i
    by_cases hi : (i : ℕ) = 0
    · simp only [Action.apply, fullCfg, hi, if_pos, SignType.coe_one]
      omega
    · simp [Action.apply, fullCfg, hi]

/-- The input rewind's unconditional first move. -/
private theorem rwIn0_step (hek : 0 < Em.k) (x : List Bool) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.step
        (fullCfg Em Gm x .rwInput0 (x.length + 1) (by omega) 0) =
      fullCfg Em Gm x .rwInput x.length (by omega) 0 := by
  rw [control_step' (mv := .neg) (r := BodyState.rwInput) (fun _ _ => rfl) rfl]
  refine Cfg.ext rfl ?_ rfl rfl rfl
  show moveInputPos (⟨x.length + 1, by omega⟩ : Fin (x.length + 2)) .neg = _
  rw [moveInputPos_neg_of_ne_left _ (by
    intro h
    have := congrArg Fin.val h
    simp at this)]
  rfl

/-- One input-rewind step over an input symbol.
**Proof sketch.** At interior position `p ≥ 1` the input read is the
`(p-1)`-st bit, so the rewind keeps moving left
(`moveInputPos_neg_of_ne_left`); nothing else changes. -/
private theorem rwInput_some (hek : 0 < Em.k) (x : List Bool) (p : ℕ)
    (hp1 : 1 ≤ p) (hpn : p ≤ x.length) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.step
        (fullCfg Em Gm x .rwInput p (by omega) 0) =
      fullCfg Em Gm x .rwInput (p - 1) (by omega) 0 := by
  have hinp : (fullCfg Em Gm x .rwInput p (by omega) 0).inputSymbol = some x[p - 1] :=
    inputSymbolInner (p - 1) (by simp only [fullCfg]; omega) (by omega)
  have h1 : (emitIterBody Em Gm hek ee ex ge gx).tm.step
      (fullCfg Em Gm x .rwInput p (by omega) 0) =
      ((emitIterBody Em Gm hek ee ex ge gx).tm.tr .rwInput
        (fullCfg Em Gm x .rwInput p (by omega) 0).inputSymbol
        (fullCfg Em Gm x .rwInput p (by omega) 0).workTapeSymbols).apply
        (fullCfg Em Gm x .rwInput p (by omega) 0) := rfl
  rw [h1, hinp]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · show moveInputPos (⟨p, by omega⟩ : Fin (x.length + 2)) .neg = _
    rw [moveInputPos_neg_of_ne_left _ (by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega)]
    rfl
  · funext i
    by_cases hi : (i : ℕ) = 0 <;>
      simp [emitIterBody, FinTM.controlAction, Action.apply, fullCfg, hi]
  · funext i
    by_cases hi : (i : ℕ) = 0 <;>
      simp [emitIterBody, FinTM.controlAction, Action.apply, fullCfg, hi]

/-- The input rewind reaches the left boundary and enters the anchor seam.
**Proof sketch.** At position zero the input read is blank, so the final
branch fires: the head steps right to the canonical position one and control
enters the anchor; the resulting configuration is literally the
`Cfg.ofWords` seam carrying the copied input on tape zero. -/
private theorem rwInput_zero (hek : 0 < Em.k) (x : List Bool) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.step
        (fullCfg Em Gm x .rwInput 0 (by omega) 0) =
      Cfg.ofWords .anchor (stateWord (max Em.k Gm.k) x) := by
  have hinp : (fullCfg Em Gm x .rwInput 0 (by omega) 0).inputSymbol = none := by
    simp only [fullCfg, Cfg.inputSymbol]
    rw [dif_pos (by apply Fin.ext; simp)]
  have h1 : (emitIterBody Em Gm hek ee ex ge gx).tm.step
      (fullCfg Em Gm x .rwInput 0 (by omega) 0) =
      ((emitIterBody Em Gm hek ee ex ge gx).tm.tr .rwInput
        (fullCfg Em Gm x .rwInput 0 (by omega) 0).inputSymbol
        (fullCfg Em Gm x .rwInput 0 (by omega) 0).workTapeSymbols).apply
        (fullCfg Em Gm x .rwInput 0 (by omega) 0) := rfl
  rw [h1, hinp]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · show moveInputPos (⟨0, by omega⟩ : Fin (x.length + 2)) .pos = _
    rw [moveInputPos_pos_of_ne_right _ (by simp)]
    apply Fin.ext
    simp [Cfg.ofWords]
  · funext i
    by_cases hi : (i : ℕ) = 0
    · simp [emitIterBody, FinTM.controlAction, Action.apply, fullCfg, Cfg.ofWords,
        stateWord, hi]
    · simp [emitIterBody, FinTM.controlAction, Action.apply, fullCfg, Cfg.ofWords,
        stateWord, hi]
  · funext i
    by_cases hi : (i : ℕ) = 0 <;>
      simp [emitIterBody, FinTM.controlAction, Action.apply, fullCfg, Cfg.ofWords, hi]

/-- **The startup segment.** From its initial configuration the body copies
the input onto tape zero, rewinds both heads, and enters the anchor seam
carrying the input, within `3·|x| + 4` steps and without visiting the anchor
earlier.
**Proof sketch.** Chain the safe runs of the four phases: `|x|` copy steps,
the boundary turnaround, `|x| + 1` tape-rewind steps, the unconditional
input-rewind entry, and `|x| + 1` input-rewind steps, each phase by
induction on its counter; every visited state is a copier state, never the
anchor. -/
private theorem body_start (hek : 0 < Em.k) :
    SafeRun (emitIterBody Em Gm hek ee ex ge gx).tm .anchor
      ((emitIterBody Em Gm hek ee ex ge gx).tm.initCfg x) (3 * x.length + 4)
      (Cfg.ofWords .anchor (stateWord (max Em.k Gm.k) x)) := by
  have hcopy : ∀ i (hi : i ≤ x.length),
      SafeRun (emitIterBody Em Gm hek ee ex ge gx).tm .anchor
        (copyCfg Em Gm x 0 (Nat.zero_le _)) i (copyCfg Em Gm x i hi) := by
    intro i
    induction i with
    | zero => intro _; exact SafeRun.zero
    | succ i ih =>
      intro hi
      exact SafeRun.trans (ih (by omega))
        (SafeRun.cons (copy_step Em Gm ee ex ge gx hek x i (by omega))
          (by simp [copyCfg]) SafeRun.zero)
  have hrwt : ∀ j (hj : j ≤ x.length),
      SafeRun (emitIterBody Em Gm hek ee ex ge gx).tm .anchor
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) ((j : ℤ) - 1)) (j + 1)
        (fullCfg Em Gm x .rwInput0 (x.length + 1) (by omega) 0) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [show ((0 : ℕ) : ℤ) - 1 = -1 from by omega]
      exact SafeRun.cons (rwTape_none Em Gm ee ex ge gx hek x) (by simp [fullCfg])
        SafeRun.zero
    | succ j ih =>
      intro hj
      rw [show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) from by push_cast; ring]
      exact SafeRun.cons (rwTape_some Em Gm ee ex ge gx hek x j (by omega))
        (by simp [fullCfg]) (ih (by omega))
  have hrwi : ∀ p (hp : p ≤ x.length),
      SafeRun (emitIterBody Em Gm hek ee ex ge gx).tm .anchor
        (fullCfg Em Gm x .rwInput p (by omega) 0) (p + 1)
        (Cfg.ofWords .anchor (stateWord (max Em.k Gm.k) x)) := by
    intro p
    induction p with
    | zero =>
      intro _
      exact SafeRun.cons (rwInput_zero Em Gm ee ex ge gx hek x) (by simp [fullCfg])
        SafeRun.zero
    | succ p ih =>
      intro hp
      exact SafeRun.cons (rwInput_some Em Gm ee ex ge gx hek x (p + 1) (by omega) hp)
        (by simp [fullCfg]) (ih (by omega))
  have hchain := ((((hcopy x.length le_rfl).trans
    (SafeRun.cons (copy_end Em Gm ee ex ge gx hek x) (by simp [copyCfg]) SafeRun.zero)).trans
    (hrwt x.length le_rfl)).trans
    (SafeRun.cons (rwIn0_step Em Gm ee ex ge gx hek x) (by simp [fullCfg]) SafeRun.zero)).trans
    (hrwi x.length le_rfl)
  rw [initCfg_eq_copyCfg]
  rw [show 3 * x.length + 4 =
    x.length + (0 + 1) + (x.length + 1) + (0 + 1) + (x.length + 1) from by omega]
  exact hchain

end Body

/-- Emit and concatenate the chunks of a bounded word iteration. The caller
supplies a machine computing the binary iteration bound `R n` in polynomial
time. The startup and per-round costs are polynomial in the input length, and
the total time includes a separate factor `R n + 2`.

**Proof sketch.** Use the existing emitting loop with clean calls to the step
and chunk machines. The orbit envelope bounds the length of each call's input
and hence the call time, including scratch cleanup. The startup and fuel
costs and both round calls are bounded by a polynomial, which leaves the
number of rounds as a separate factor. -/
theorem FinTM.exists_emitIterTM_withFuel (G E F : FinTM Bool) (g e : List Bool → List Bool)
    (CG cG CE cE CF cF : ℕ) (R : ℕ → ℕ)
    (hG : G.ComputesFunInTime g (fun n => CG * (n + 1) ^ cG))
    (hE : E.ComputesFunInTime e (fun n => CE * (n + 1) ^ cE))
    (hF : F.ComputesFunInTime (fun w => Nat.bits (R w.length)) (fun n => CF * (n + 1) ^ cF))
    (b l : ℕ)
    (horbit : ∀ (w : List Bool) (i : ℕ), (g^[i] w).length ≤ b * (w.length + 1) ^ l) :
    ∃ (M : FinTM Bool) (C c : ℕ),
      M.ComputesFunInTime
        (fun w => (List.range (R w.length + 1)).flatMap (fun i => e (g^[i] w)))
        (fun n => C * (n + 1) ^ c * (R n + 2)) := by
  classical
  obtain ⟨Ce, eentry, eexit, cEcall, hke, hEcall⟩ :=
    FinTM.exists_emitCallTM E e _ hE
  obtain ⟨Cg, gentry, gexit, cGcall, hkg, hGcall⟩ :=
    FinTM.exists_installCallTM G g _ hG
  -- output-length bounds from the one-symbol-per-step discipline
  have hElen : ∀ s : List Bool, (e s).length ≤ CE * (s.length + 1) ^ cE := by
    intro s
    have hout := ((FinTM.computesInTime_iff _ _ _ _).mp
      ((FinTM.computesFunInTime_iff _ _ _).1 hE s)).2
    simpa only [hout] using E.tm.output_length_le s (CE * (s.length + 1) ^ cE)
  have hGlen : ∀ s : List Bool, (g s).length ≤ CG * (s.length + 1) ^ cG := by
    intro s
    have hout := ((FinTM.computesInTime_iff _ _ _ _).mp
      ((FinTM.computesFunInTime_iff _ _ _).1 hG s)).2
    simpa only [hout] using G.tm.output_length_le s (CG * (s.length + 1) ^ cG)
  -- the budget
  set L : ℕ → ℕ := fun n => b * (n + 1) ^ l with hL
  set TEb : ℕ → ℕ := fun n => CE * (L n + 1) ^ cE with hTEb
  set TGb : ℕ → ℕ := fun n => CG * (L n + 1) ^ cG with hTGb
  set T : ℕ → ℕ := fun n => CF * (n + 1) ^ cF + (3 * n + 4) +
    (cEcall * (2 * TEb n + L n + 1) + cGcall * (2 * TGb n + L n + 1) + 2) with hT
  set body := emitIterBody Ce Cg hke eentry eexit gentry gexit with hbody
  have hF' : F.ComputesFunInTime
      (fun x => Nat.bits (R x.length)) T := by
    refine (FinTM.computesFunInTime_iff _ _ _).2 fun x => ?_
    refine ((FinTM.computesFunInTime_iff _ _ _).1 hF x).mono ?_
    simp only [hT]
    omega
  have hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ t' < t, (body.tm.runFrom (body.tm.initCfg x) t').state ≠
        some BodyState.anchor) ∧
      body.tm.runFrom (body.tm.initCfg x) t =
        Cfg.ofWords .anchor (stateWord body.k x) := by
    intro x
    obtain ⟨hrun, hsafe⟩ := safeRun_iff.1 <| body_start Ce Cg eentry eexit gentry gexit hke (x := x)
    exact ⟨3 * x.length + 4, by simp only [hT]; omega, hsafe, hrun⟩
  have hround : ∀ (x s : List Bool), (∃ i, s = g^[i] x) →
      ∃ t, 0 < t ∧ t ≤ T x.length ∧
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom
            (Cfg.ofWords (input := x) .anchor (stateWord body.k s)) t').state ≠
              some BodyState.anchor) ∧
        body.tm.runFrom
          (Cfg.ofWords (input := x) .anchor (stateWord body.k s)) t =
            { Cfg.ofWords .anchor (stateWord body.k (g s)) with output := e s } := by
    rintro x s ⟨i, rfl⟩
    set s := g^[i] x with hs
    have hsL : s.length ≤ L x.length := horbit x i
    obtain ⟨tEc, htEb', htEpos, hEfirst, hErun⟩ := hEcall x s
    obtain ⟨tGc, htGb', htGpos, hGfirst, hGrun⟩ := hGcall x s
    obtain ⟨hrun, hsafe⟩ := body_round Ce Cg eentry eexit gentry gexit hke hkg
      (x := x) s (e s) (g s) tEc htEpos hEfirst hErun tGc htGpos hGfirst hGrun
    refine ⟨tEc + 1 + tGc + 1, by omega, ?_, hsafe, hrun⟩
    have hpow : s.length + 1 ≤ L x.length + 1 := by omega
    have hTEs : CE * (s.length + 1) ^ cE ≤ TEb x.length :=
      Nat.mul_le_mul_left CE (Nat.pow_le_pow_left hpow cE)
    have hTGs : CG * (s.length + 1) ^ cG ≤ TGb x.length :=
      Nat.mul_le_mul_left CG (Nat.pow_le_pow_left hpow cG)
    have hes := hElen s
    have hgs := hGlen s
    have htE2 : tEc ≤ cEcall * (2 * TEb x.length + L x.length + 1) :=
      le_trans htEb' (Nat.mul_le_mul_left cEcall (by omega))
    have htG2 : tGc ≤ cGcall * (2 * TGb x.length + L x.length + 1) :=
      le_trans htGb' (Nat.mul_le_mul_left cGcall (by omega))
    simp only [hT]
    omega
  obtain ⟨M, c, hM⟩ := FinTM.exists_emitLoopTM body F .anchor
    (fun w s => ∃ i, s = g^[i] w) (fun _ s => g s) (fun _ s => e s)
    (fun w => w) R T hF'
    (fun w => ⟨0, rfl⟩)
    (fun w s hs => by
      obtain ⟨i, rfl⟩ := hs
      exact ⟨i + 1, (Function.iterate_succ_apply' g i w).symm⟩)
    hstart hround
  -- polynomial normal form
  set D : ℕ := cF + l * cE + l * cG + l + 1 with hD
  have honeD : ∀ n : ℕ, 1 ≤ (n + 1) ^ D := fun n => Nat.one_le_pow _ _ (by omega)
  have hTle : ∀ n, T n ≤
      (CF + 4 + cEcall * (2 * CE * (b + 1) ^ cE + b + 2) +
        cGcall * (2 * CG * (b + 1) ^ cG + b + 2) + 2) * (n + 1) ^ D := by
    intro n
    have hone : 1 ≤ (n + 1) ^ l := Nat.one_le_pow _ _ (by omega)
    have hLb : L n + 1 ≤ (b + 1) * (n + 1) ^ l := by
      simp only [hL]
      calc b * (n + 1) ^ l + 1 ≤ b * (n + 1) ^ l + (n + 1) ^ l := by omega
        _ = (b + 1) * (n + 1) ^ l := by ring
    have hpowD : ∀ a : ℕ, a ≤ D → (n + 1) ^ a ≤ (n + 1) ^ D :=
      fun a ha => Nat.pow_le_pow_right (by omega) ha
    have hTEbn : TEb n ≤ CE * (b + 1) ^ cE * (n + 1) ^ (l * cE) := by
      simp only [hTEb]
      calc CE * (L n + 1) ^ cE ≤ CE * ((b + 1) * (n + 1) ^ l) ^ cE :=
            Nat.mul_le_mul_left CE (Nat.pow_le_pow_left hLb cE)
        _ = CE * (b + 1) ^ cE * (n + 1) ^ (l * cE) := by
            rw [mul_pow, ← pow_mul]
            ring
    have hTGbn : TGb n ≤ CG * (b + 1) ^ cG * (n + 1) ^ (l * cG) := by
      simp only [hTGb]
      calc CG * (L n + 1) ^ cG ≤ CG * ((b + 1) * (n + 1) ^ l) ^ cG :=
            Nat.mul_le_mul_left CG (Nat.pow_le_pow_left hLb cG)
        _ = CG * (b + 1) ^ cG * (n + 1) ^ (l * cG) := by
            rw [mul_pow, ← pow_mul]
            ring
    have h1 : CF * (n + 1) ^ cF ≤ CF * (n + 1) ^ D :=
      Nat.mul_le_mul_left CF (hpowD _ (by omega))
    have h2 : 3 * n + 4 ≤ 4 * (n + 1) ^ D := by
      have : n + 1 ≤ (n + 1) ^ D := le_trans (by omega)
        (Nat.le_self_pow (by omega) (n + 1))
      omega
    have h3 : TEb n ≤ CE * (b + 1) ^ cE * (n + 1) ^ D :=
      le_trans hTEbn (Nat.mul_le_mul_left _ (hpowD _ (by omega)))
    have h4 : TGb n ≤ CG * (b + 1) ^ cG * (n + 1) ^ D :=
      le_trans hTGbn (Nat.mul_le_mul_left _ (hpowD _ (by omega)))
    have h5 : L n + 1 ≤ (b + 1) * (n + 1) ^ D :=
      le_trans hLb (Nat.mul_le_mul_left _ (hpowD _ (by omega)))
    have hE3 : cEcall * (2 * TEb n + L n + 1) ≤
        cEcall * (2 * CE * (b + 1) ^ cE + b + 2) * (n + 1) ^ D := by
      rw [Nat.mul_assoc]
      refine Nat.mul_le_mul_left cEcall ?_
      calc 2 * TEb n + L n + 1 ≤
            2 * (CE * (b + 1) ^ cE * (n + 1) ^ D) + (b + 1) * (n + 1) ^ D +
              (n + 1) ^ D := by
            have := honeD n
            omega
        _ = (2 * CE * (b + 1) ^ cE + b + 2) * (n + 1) ^ D := by ring
    have hG3 : cGcall * (2 * TGb n + L n + 1) ≤
        cGcall * (2 * CG * (b + 1) ^ cG + b + 2) * (n + 1) ^ D := by
      rw [Nat.mul_assoc]
      refine Nat.mul_le_mul_left cGcall ?_
      calc 2 * TGb n + L n + 1 ≤
            2 * (CG * (b + 1) ^ cG * (n + 1) ^ D) + (b + 1) * (n + 1) ^ D +
              (n + 1) ^ D := by
            have := honeD n
            omega
        _ = (2 * CG * (b + 1) ^ cG + b + 2) * (n + 1) ^ D := by ring
    have h6 : 2 ≤ 2 * (n + 1) ^ D := by
      have := honeD n
      omega
    simp only [hT]
    calc CF * (n + 1) ^ cF + (3 * n + 4) +
          (cEcall * (2 * TEb n + L n + 1) + cGcall * (2 * TGb n + L n + 1) + 2) ≤
        CF * (n + 1) ^ D + 4 * (n + 1) ^ D +
          (cEcall * (2 * CE * (b + 1) ^ cE + b + 2) * (n + 1) ^ D +
            cGcall * (2 * CG * (b + 1) ^ cG + b + 2) * (n + 1) ^ D +
            2 * (n + 1) ^ D) :=
          Nat.add_le_add (Nat.add_le_add h1 h2)
            (Nat.add_le_add (Nat.add_le_add hE3 hG3) h6)
      _ = (CF + 4 + cEcall * (2 * CE * (b + 1) ^ cE + b + 2) +
            cGcall * (2 * CG * (b + 1) ^ cG + b + 2) + 2) * (n + 1) ^ D := by ring
  set K₀ : ℕ := CF + 4 + cEcall * (2 * CE * (b + 1) ^ cE + b + 2) +
    cGcall * (2 * CG * (b + 1) ^ cG + b + 2) + 2 with hK₀
  refine ⟨M, c * (K₀ + 1), D, (FinTM.computesFunInTime_iff _ _ _).2 fun w => ?_⟩
  have hMw := (FinTM.computesFunInTime_iff _ _ _).1 hM w
  refine hMw.mono ?_
  set n := w.length
  have hT1 : T n + 1 ≤ (K₀ + 1) * (n + 1) ^ D := by
    have h := hTle n
    have h1 := honeD n
    calc T n + 1 ≤ K₀ * (n + 1) ^ D + (n + 1) ^ D := by omega
      _ = (K₀ + 1) * (n + 1) ^ D := by ring
  calc c * (T n + 1) * (R n + 2) ≤ c * ((K₀ + 1) * (n + 1) ^ D) * (R n + 2) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left c hT1)
    _ = c * (K₀ + 1) * (n + 1) ^ D * (R n + 2) := by ring

/-- **The emit-iteration machine** ([AB09] §7.3–§7.4 folklore: simulate a
machine on polynomially many rounds and concatenate the outcomes).  Given
machines computing the step `g` and the chunk `e` within polynomial budgets,
and a polynomial length envelope for the orbit of `g`, one finite machine
computes the concatenation of the chunks `e (g^[i] w)` for
`i = 0, …, a'·(|w|+1)^k'`, within a polynomial budget in the `C·(n+1)^c`
normal form.

**Proof sketch.** Apply the fuel-machine version to the polynomial-bits
machine, then bound the product of the per-round polynomial and the number
of rounds by one normal-form polynomial. -/
theorem FinTM.exists_emitIterTM (G E : FinTM Bool) (g e : List Bool → List Bool)
    (CG cG CE cE : ℕ)
    (hG : G.ComputesFunInTime g (fun n => CG * (n + 1) ^ cG))
    (hE : E.ComputesFunInTime e (fun n => CE * (n + 1) ^ cE))
    (a' k' b l : ℕ)
    (horbit : ∀ (w : List Bool) (i : ℕ), (g^[i] w).length ≤ b * (w.length + 1) ^ l) :
    ∃ (M : FinTM Bool) (C c : ℕ),
      M.ComputesFunInTime
        (fun w => (List.range (a' * (w.length + 1) ^ k' + 1)).flatMap
          (fun i => e (g^[i] w)))
        (fun n => C * (n + 1) ^ c) := by
  obtain ⟨F, cF, hF⟩ := FinTM.computesFunInTime_polyBits a' k'
  obtain ⟨M, C, D, hM⟩ :=
    FinTM.exists_emitIterTM_withFuel G E F g e CG cG CE cE cF (k' + 1)
      (fun n => a' * (n + 1) ^ k') hG hE hF b l horbit
  refine ⟨M, C * (a' + 2), D + k', (FinTM.computesFunInTime_iff _ _ _).2 fun w => ?_⟩
  refine ((FinTM.computesFunInTime_iff _ _ _).1 hM w).mono ?_
  let n := w.length
  have hR : a' * (n + 1) ^ k' + 2 ≤ (a' + 2) * (n + 1) ^ k' := by
    have hpos : 1 ≤ (n + 1) ^ k' := Nat.one_le_pow _ _ (by omega)
    rw [Nat.add_mul]
    omega
  calc C * (n + 1) ^ D * (a' * (n + 1) ^ k' + 2)
      ≤ C * (n + 1) ^ D * ((a' + 2) * (n + 1) ^ k') := Nat.mul_le_mul_left _ hR
    _ = C * (a' + 2) * (n + 1) ^ (D + k') := by rw [pow_add]; ring

end Turing

## ===== TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean =====

/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.TuringMachine.Build.Loop
import TCSlib.Complexity.TuringMachine.Build.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Run embedding for loop bodies

Generic machine-construction infrastructure shared by loop-body assemblies
(first customer: `TCSlib.Complexity.TuringMachine.Build.EmitIterBody`):

* **safe runs** — a run segment that never visits an avoided (anchor) state
  strictly before its endpoint, closed under prepending a step and under
  concatenation: the shape of the `Turing.FinTM.exists_emitLoopTM` startup
  and round obligations;
* **output-prefix commutation** — the transition table never reads the
  output tape and the output is append-only, so prepending a fixed output
  prefix commutes with running the machine, and outputs only ever extend;
* **the tape-padding, state-injecting embedding** — a clean-call module over
  `m ≤ k` tapes runs inside a `k`-tape host on its first `m` work tapes with
  its states injected into the host's state type, step for step
  (`embed_step`/`embed_run`), while the padding tapes stay blank;
* **control steps** — a transition that only changes control (and possibly
  moves the input head) replaces just those configuration components. These
  two lemmas are private helpers of
  `TCSlib.Complexity.TuringMachine.Build.EmitIterBody`, not exports of this
  module.

## Main definitions

* `Turing.SafeRun` (read through `Turing.safeRun_iff`), `Turing.padAction`, `Turing.embedCfg`.

## Main results

* `Turing.runFrom_output_prefix`, `Turing.runFrom_output_extends`,
  `Turing.embed_run`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the machine model these
  constructions assemble.)
-/

namespace Turing

open MultiTapeTM

variable {k m : ℕ} {B SS : Type} {x : List Bool}

/-! ### Safe runs

A run segment together with the promise that no strictly earlier
configuration sits at the avoided (anchor) state: the shape of the
`exists_emitLoopTM` startup and round obligations, closed under
single-step prepending and concatenation. -/

/-- A run from `c` to `c'` in exactly `t` steps that never visits the state
`avoid` strictly before `t`. -/
def SafeRun (H : MultiTapeTM k Bool B) (avoid : B)
    (c : Cfg k Bool B x) (t : ℕ) (c' : Cfg k Bool B x) : Prop :=
  H.runFrom c t = c' ∧ ∀ t' < t, (H.runFrom c t').state ≠ some avoid

/-- `SafeRun H avoid c t c' ↔ H.runFrom c t = c' ∧ ∀ t' < t, (H.runFrom c t').state ≠ some avoid`:
the published reading of `Turing.SafeRun`. -/
theorem safeRun_iff {H : MultiTapeTM k Bool B} {avoid : B} {c : Cfg k Bool B x} {t : ℕ}
    {c' : Cfg k Bool B x} :
    SafeRun H avoid c t c' ↔
      H.runFrom c t = c' ∧ ∀ t' < t, (H.runFrom c t').state ≠ some avoid :=
  Iff.rfl

/-- The empty run is safe. -/
theorem SafeRun.zero {H : MultiTapeTM k Bool B} {avoid : B}
    {c : Cfg k Bool B x} : SafeRun H avoid c 0 c :=
  ⟨rfl, fun t' ht' => absurd ht' (by omega)⟩

/-- Prepend one non-avoided step to a safe run. -/
theorem SafeRun.cons {H : MultiTapeTM k Bool B} {avoid : B}
    {c c₁ c' : Cfg k Bool B x} {t : ℕ} (hstep : H.step c = c₁)
    (hc : c.state ≠ some avoid) (h : SafeRun H avoid c₁ t c') :
    SafeRun H avoid c (t + 1) c' := by
  have hone : H.runFrom c 1 = c₁ := by
    simp [runFrom, hstep]
  refine ⟨?_, ?_⟩
  · rw [show t + 1 = 1 + t by omega, runFrom_add, hone]
    exact h.1
  · intro t' ht'
    cases t' with
    | zero => simpa using hc
    | succ u =>
      rw [show u + 1 = 1 + u by omega, runFrom_add, hone]
      exact h.2 u (by omega)

/-- Concatenate safe runs. -/
theorem SafeRun.trans {H : MultiTapeTM k Bool B} {avoid : B}
    {c c₁ c' : Cfg k Bool B x} {t₁ t₂ : ℕ} (h₁ : SafeRun H avoid c t₁ c₁)
    (h₂ : SafeRun H avoid c₁ t₂ c') : SafeRun H avoid c (t₁ + t₂) c' := by
  refine ⟨?_, ?_⟩
  · rw [runFrom_add, h₁.1]
    exact h₂.1
  · intro t' ht'
    by_cases hlt : t' < t₁
    · exact h₁.2 t' hlt
    · obtain ⟨u, rfl⟩ : ∃ u, t' = t₁ + u := ⟨t' - t₁, by omega⟩
      rw [runFrom_add, h₁.1]
      exact h₂.2 u (by omega)

/-! ### Output-prefix commutation

The transition table never reads the output tape and the output is
append-only, so prepending a fixed prefix to the output commutes with
running the machine. -/

/-- One step commutes with an output prefix. -/
theorem step_output_prefix (H : MultiTapeTM k Bool B)
    (c : Cfg k Bool B x) (pre : List Bool) :
    H.step { c with output := pre ++ c.output } =
      { H.step c with output := pre ++ (H.step c).output } := by
  obtain ⟨st, pos, tapes, tpos, out⟩ := c
  cases st with
  | none => rfl
  | some q =>
    have hws : (⟨some q, pos, tapes, tpos, pre ++ out⟩ : Cfg k Bool B x).workTapeSymbols =
        (⟨some q, pos, tapes, tpos, out⟩ : Cfg k Bool B x).workTapeSymbols := rfl
    simp [MultiTapeTM.step, Action.apply, Cfg.inputSymbol, hws, List.append_assoc]

/-- A run commutes with an output prefix. -/
theorem runFrom_output_prefix (H : MultiTapeTM k Bool B)
    (c : Cfg k Bool B x) (pre : List Bool) (t : ℕ) :
    H.runFrom { c with output := pre ++ c.output } t =
      { H.runFrom c t with output := pre ++ (H.runFrom c t).output } := by
  induction t generalizing c with
  | zero => simp
  | succ t ih =>
    rw [runFrom_succ_eq_step, runFrom_succ_eq_step, step_output_prefix]
    exact ih (H.step c)

/-- The output tape is append-only along a run. -/
theorem runFrom_output_extends (H : MultiTapeTM k Bool B)
    (c : Cfg k Bool B x) (t : ℕ) :
    ∃ o, (H.runFrom c t).output = c.output ++ o := by
  induction t generalizing c with
  | zero => exact ⟨[], by simp⟩
  | succ t ih =>
    rw [runFrom_succ_eq_step]
    obtain ⟨o, ho⟩ := ih (H.step c)
    unfold MultiTapeTM.step at ho ⊢
    cases hq : c.state with
    | none =>
      rw [hq] at ho
      exact ⟨o, ho⟩
    | some q =>
      rw [hq] at ho
      refine ⟨(H.tr q c.inputSymbol c.workTapeSymbols).output.toList ++ o, ?_⟩
      rw [ho]
      simp [Action.apply]

/-! ### Halted runs are stationary -/

/-- A halted configuration never changes. -/
theorem runFrom_of_halted (H : MultiTapeTM k Bool B)
    {c : Cfg k Bool B x} (h : c.state = none) (t : ℕ) : H.runFrom c t = c := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [runFrom_add, ih]
    simp [runFrom, step_of_halt h]

/-- Every configuration strictly before a live endpoint is live. -/
theorem state_isSome_of_runFrom (H : MultiTapeTM k Bool B)
    {c : Cfg k Bool B x} {t : ℕ} {qf : B}
    (hf : (H.runFrom c t).state = some qf) {j : ℕ} (hj : j ≤ t) :
    ∃ q, (H.runFrom c j).state = some q := by
  cases hq : (H.runFrom c j).state with
  | some q => exact ⟨q, rfl⟩
  | none =>
    exfalso
    have hstat : H.runFrom c t = H.runFrom c j := by
      obtain ⟨u, rfl⟩ : ∃ u, t = j + u := ⟨t - j, by omega⟩
      rw [runFrom_add, runFrom_of_halted H hq]
    rw [hstat, hq] at hf
    exact Option.noConfusion hf

/-! ### Tape-padding, state-injecting embedding

A clean-call module over `m ≤ k` tapes runs inside the `k`-tape body on its
first `m` work tapes, with its states injected into the body's state type;
the extra tapes stay blank and their heads stay at the origin. -/

/-- Pad a module action to the host: act on the first `m` tapes, leave the
rest alone, and map the successor state. -/
def padAction (hmk : m ≤ k) (f : Option SS → Option B)
    (a : Action m Bool SS) : Action k Bool B where
  inputTape := a.inputTape
  workTapes := fun i =>
    if h : (i : ℕ) < m then a.workTapes ⟨i, h⟩ else (none, 0)
  output := a.output
  state := f a.state

/-- Embed a module configuration into the host. -/
def embedCfg (hmk : m ≤ k) (inject : SS → B)
    (c : Cfg m Bool SS x) : Cfg k Bool B x where
  state := c.state.map inject
  inputPos := c.inputPos
  workTapes := fun i =>
    if h : (i : ℕ) < m then c.workTapes ⟨i, h⟩ else fun _ => none
  workTapePos := fun i =>
    if h : (i : ℕ) < m then c.workTapePos ⟨i, h⟩ else 0
  output := c.output

/-- Embedding a canonical seam gives a canonical seam with the padded word
assignment. -/
theorem embedCfg_ofWords (hmk : m ≤ k) (inject : SS → B) (q : SS)
    (w : Fin m → List Bool) :
    embedCfg hmk inject (Cfg.ofWords (input := x) q w) =
      Cfg.ofWords (inject q)
        (fun i => if h : (i : ℕ) < m then w ⟨i, h⟩ else []) := by
  unfold embedCfg Cfg.ofWords
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases h : (i : ℕ) < m <;> simp [h]
  · funext i
    by_cases h : (i : ℕ) < m <;> simp [h]

/-- Applying a padded action to an embedded configuration embeds the applied
module configuration. -/
theorem padAction_apply (hmk : m ≤ k) (inject : SS → B)
    (a : Action m Bool SS) (c : Cfg m Bool SS x) (b : B) :
    (padAction hmk (Option.map inject) a).apply
        { embedCfg hmk inject c with state := some b } =
      embedCfg hmk inject (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases h : (i : ℕ) < m
    · simp only [Action.apply, padAction, embedCfg, dif_pos h]
    · simp only [Action.apply, padAction, embedCfg, dif_neg h]
  · funext i
    by_cases h : (i : ℕ) < m
    · simp only [Action.apply, padAction, embedCfg, dif_pos h]
    · simp only [Action.apply, padAction, embedCfg, dif_neg h]
      rfl

/-- The embedded configuration reads the module's work symbols on the first
`m` tapes. -/
theorem embedCfg_workTapeSymbols (hmk : m ≤ k) (inject : SS → B)
    (c : Cfg m Bool SS x) (b : B) :
    (fun i => ({ embedCfg hmk inject c with state := some b } :
        Cfg k Bool B x).workTapeSymbols (Fin.castLE hmk i)) =
      c.workTapeSymbols := by
  funext i
  have h : ((Fin.castLE hmk i : Fin k) : ℕ) < m := i.isLt
  simp only [Cfg.workTapeSymbols, embedCfg, dif_pos h]
  congr 1 <;> exact congrArg _ (Fin.eta i i.isLt) <;> rfl

/-- Embedding commutes with replacing the output. -/
theorem embedCfg_output (hmk : m ≤ k) (inject : SS → B)
    (c : Cfg m Bool SS x) (o : List Bool) :
    embedCfg hmk inject { c with output := o } =
      { embedCfg hmk inject c with output := o } := rfl

/-- A one-step run is a step. -/
theorem runFrom_one (H : MultiTapeTM k Bool B) (c : Cfg k Bool B x) :
    H.runFrom c 1 = H.step c := by
  simp [MultiTapeTM.runFrom]

/-- One host step at a state behaving like the module's state `q` tracks one
module step.
**Proof sketch.** Both steps dispatch their transition tables on live states;
the embedded configuration reads the same input symbol and, through
`embedCfg_workTapeSymbols`, the same work symbols, so the host's action is
the padded module action, and `padAction_apply` pushes it through the
embedding. -/
theorem embed_step (hmk : m ≤ k) (M : MultiTapeTM m Bool SS)
    (H : MultiTapeTM k Bool B) (inject : SS → B)
    (c : Cfg m Bool SS x) (q : SS) (hq : c.state = some q) (b : B)
    (htr : ∀ inp work, H.tr b inp work =
      padAction hmk (Option.map inject)
        (M.tr q inp (fun i => work (Fin.castLE hmk i)))) :
    H.step { embedCfg hmk inject c with state := some b } =
      embedCfg hmk inject (M.step c) := by
  have hIS : ({ embedCfg hmk inject c with state := some b } :
      Cfg k Bool B x).inputSymbol = c.inputSymbol := rfl
  have hstepL : H.step { embedCfg hmk inject c with state := some b } =
      (H.tr b ({ embedCfg hmk inject c with state := some b } :
          Cfg k Bool B x).inputSymbol
        ({ embedCfg hmk inject c with state := some b } :
          Cfg k Bool B x).workTapeSymbols).apply
        { embedCfg hmk inject c with state := some b } := rfl
  have hstepR : M.step c = (M.tr q c.inputSymbol c.workTapeSymbols).apply c := by
    unfold MultiTapeTM.step
    rw [hq]
  rw [hstepL, hstepR, htr, hIS, embedCfg_workTapeSymbols]
  exact padAction_apply hmk inject _ c b

/-- A module run strictly inside the avoided exit embeds step-for-step into
the host, provided the host's transition at every injected live state is the
padded module transition.
**Proof sketch.** Induction on the run length: every strictly earlier
configuration is live and off the exit by hypothesis, so `embed_step`
transports each step. -/
theorem embed_run (hmk : m ≤ k) (M : MultiTapeTM m Bool SS)
    (H : MultiTapeTM k Bool B) (inject : SS → B) (ex : SS)
    (htr : ∀ q : SS, q ≠ ex → ∀ inp work,
      H.tr (inject q) inp work =
        padAction hmk (Option.map inject)
          (M.tr q inp (fun i => work (Fin.castLE hmk i))))
    (c : Cfg m Bool SS x) (t : ℕ)
    (hstate : ∀ j < t, ∃ q, (M.runFrom c j).state = some q ∧ q ≠ ex) :
    H.runFrom (embedCfg hmk inject c) t = embedCfg hmk inject (M.runFrom c t) := by
  induction t generalizing c with
  | zero => simp
  | succ t ih =>
    obtain ⟨q, hq, hqex⟩ := hstate 0 (by omega)
    simp only [runFrom_zero] at hq
    have hstep : H.step (embedCfg hmk inject c) = embedCfg hmk inject (M.step c) := by
      have hc : { embedCfg hmk inject c with state := some (inject q) } =
          embedCfg hmk inject c := by
        simp [embedCfg, hq]
      rw [← hc]
      exact embed_step hmk M H inject c q hq (inject q) (htr q hqex)
    rw [runFrom_succ_eq_step, runFrom_succ_eq_step, hstep]
    exact ih (M.step c) (fun j hj => by
      have := hstate (j + 1) (by omega)
      simpa [runFrom, Function.iterate_succ_apply] using this)


end Turing

## ===== TCSlib/Complexity/TuringMachine/Build/Primitives.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.List.Induction
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import TCSlib.Complexity.ClassP.TimeConstructible
import TCSlib.Complexity.TuringMachine.Build.Convention
import TCSlib.Complexity.TuringMachine.Build.Loop
import TCSlib.Complexity.TuringMachine.Build.Wrappers
import TCSlib.Complexity.TuringMachine.Composition
import TCSlib.Complexity.TuringMachine.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: the primitive catalog

The instruction set of the machine-construction library
(`machine-library-design.md` §4, P1–P12): the timed string functions every
Chapter-2 fill batch privately rebuilt, stated once as machine contracts.
`Turing.FinTM.computesFunInTime_id` and
`Turing.FinTM.computesFunInTime_const` (in
`TCSlib.Complexity.TuringMachine.Composition`) are catalog entries P1–P2
and already proved; this module states the rest.

**Status: proved.** Every theorem below is proved; roughly half were
harvests — their fills adapted already-proved private constructions from
the Chapter-2 epoch-2 batches (named per entry) — and the rest are new
small machines. Following the house idiom of
`TCSlib.Complexity.TuringMachine.Composition`, the contracts are
existentially packaged; each fill implements a named private machine with
its run invariants and closes the existential. Multi-argument interfaces
go through `Turing.pairEncode`, whose self-delimiting grammar lets a
pipeline stage **thread the original input through its output** — the
`pairLenCheck` and `stripLast` contracts below are deliberately stated in
that threaded form, which is exactly how the Chapter-2 verifier
constructions consume them. New Chapter-1 surface, flagged for the shared
infrastructure audit round.

**Catalog refinements at spec time** (recorded against the frozen design
§4): P6 is realized as the fixed-first-component encoder plus the threaded
extractors/validity test; P7 (replicate) is subsumed by the unary clause of
P5, whose instances are what the emission customers actually consume; P8
is realized in threaded form (`pairLenCheck`); P12 (`clearTM`) has no
standalone string-function contract — clearing is intra-machine and lives
in the loop fill's toolkit. **Round-2 additions** (per round-1 finding 3:
the extractors discard the other component by design, and sequential
composition alone never yields simultaneous access to two results): P13
`pairConcat` (the D-WRAP shape), P14 `pairDup` (the entry stage of
data-retaining pipelines), and the threaded-map combinator `pairMapSnd`;
P10's narrowing is recorded, and result-bearing search is now
`Turing.FinTM.exists_loopFindTM` (`machine-library-design.md` §9b).

## Named witnesses and their specs (MIG-1)

The rows' witnesses are public, each with its spec theorem:
* `Turing.FinTM.prependTM` (`prependTM_computes`), `incFixedTM` (`incFixedTM_computes`),
  `pairValidTM` (`pairValidTM_computes`), `pairExtractTM` (`pairExtractTM_computes`,
  `pairExtractTM_fst`, `pairExtractTM_snd`, `pairExtractTM_concat`; the first component's complete
  run, `pairExtractTM_fst_run` and `pairExtractTM_fst_run_budget`);
* `polyUnaryTM` (`polyUnaryTM_computes`, `polyUnaryTM_spaceUsed`), `polyBitsTM`
  (`polyBitsTM_computes`), `pairLenCheckTM` (`pairLenCheckTM_computes`), `stripLastTM`
  (`stripLastTM_computes`);
* `splitSolveTM` (`splitSolveTM_computes`, `splitSolveTM_spaceUsed`), `splitSolveWithTM`
  (`splitSolveWithTM_computes`);
* `unaryTokenTM` (`unaryTokenTM_computes`), `appendBitTM` (`appendBitTM_computes`).

`polyUnaryTM_spaceUsed`, `unaryTokenTM_computes` and `appendBitTM_computes` are sorried
until the fill F-B; every other spec has a proof, and the ones that cite a spec sorried until
its own fill depend on it (`polyBitsTM_computes`, `stripLastTM_computes` and the three
split-search specs).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–§1.4: all entries are the
  folklore tape subroutines of the textbook's simulation arguments.)

**Implementation note (batch P).** The first eleven targets in the batch
brief's fill order and the four continuation targets `pairLenCheck`,
`stripLast`, `pairMapSnd`, and `splitSolve` are proved. The original spec-phase
prose above and on the contracts is retained as the audit record. The length
counter is obtained from the public `Complexity.timeConstructible_id`, whose
proved machine implements precisely the sketched amortized counter. The three
extractors share one private buffered parser, so suffix-only extraction also
buffers and replays silently before copying the suffix; its linear envelope
is unchanged. The fixed-width incrementer adapts the enumerator's carry
semantics to two native-input scans, validating before physical emission.


**Implementation note (batch P2).** The threaded length checker, marker stripper,
threaded map, and split search are proved. The length checker composes the existing
buffered first extractor with the unary generator, captures the result with
`capture_run`, then reparses and counts down on the native payload. Malformed
inputs emit only `[false]`. The marker stripper first guards on a valid
extracted suffix containing a true bit; the successful branch buffers the
whole original encoding, erases its final marker/false-run, and replays the
retained encoding. The guard is complete before any physical output. Both
routes reuse the in-file parser/scan invariant patterns and proved public
wrappers. `catalogPayload_computes` supplies a proved relocated-simulation
component for the threaded map, with its time evaluated at the actual suffix
length; the retained-prefix/captured-output controller is proved below.


**Implementation note (batch P3).** The threaded map is proved.
`pairMapTM` captures `catalogPayload_computes` on the original physical input,
rewinds the capture and input, validates without emission, then replays the
original encoded prefix and captured result. `pairMap_computes` bounds this
controller by `4 * (T n + n + 3)` and the public theorem uses coefficient 40.
All original contract docstrings are retained as the audit record.

The split-search theorem is proved. Its private components include the unary
orbit/search bridges and
`splitSolve_of_body`, which closes the public result only when supplied the
actual startup and round contracts; a candidate-preserving unary-bank
preparer; a counted source-simulation correspondence; the generator's exact
loop endpoint; and a scratch-restoration controller with a positive first
return and no earlier visit to its return state. The combined `splitBodyTM`
and `splitBody_round` assemble these components and prove `hround`.
-/

/-! Batch P4 closure note: the split-search body is now constructed and proved.
`splitBodyTM` separates preparation, counted source evaluation, checked rewind,
rejection restoration, and native-bit emission into disjoint finite phases.
`splitBody_round` composes their exact seams and proves positive duration and
strict-interior anchor exclusion, including the arbitrary-bit past-end stall.
`splitEmit_run` supplies the native-slice payload; `splitBody_envelope` accounts
for every phase within the common polynomial bound. Both exponent cases
instantiate this body through the proved `splitSolve_of_body` loop closure.
All fifteen primitive contracts are now proved without admissions. Earlier
spec/checkpoint status notes above are retained as historical documentation. -/

namespace Turing.FinTM

/-! Implementation note (batch P): the private prefix construction below is
adapted in-file from `ClassNP/Reductions.lean`; no private declaration from
that module is used. Completed contracts retain their audited spec docstrings. -/

/-- **The prepending machine**. A machine with no work tapes that writes the fixed word `w` and then
copies its input, so that it computes `x ↦ w ++ x`; its last state is the copy state. [AB09, §1.2]
-/
def prependTM (w : List Bool) : FinTM Bool where
  k := 0
  State := Fin (w.length + 1)
  tm :=
    { q₀ := 0
      tr := fun q inp _ =>
        if h : q.val < w.length then
          ⟨0, fun i => i.elim0, some w[q.val], some ⟨q.val + 1, by omega⟩⟩
        else match inp with
          | some b => ⟨1, fun i => i.elim0, some b, some q⟩
          | none => ⟨0, fun i => i.elim0, none, none⟩ }

/-- A prefixing-machine configuration with the vacuous work fields suppressed. -/
private def catalogPrefixCfg (w x : List Bool) (q : Option (Fin (w.length + 1)))
    (p : Fin (x.length + 2)) (out : List Bool) : Cfg 0 Bool (Fin (w.length + 1)) x :=
  ⟨q, p, fun i => i.elim0, fun i => i.elim0, out⟩

/-- After `i` prefix steps exactly the first `i` fixed bits have been emitted,
and the input head has not moved. -/
private lemma catalogPrefixTM_emit (w x : List Bool) : ∀ i (hi : i ≤ w.length),
    (prependTM w).tm.runFrom ((prependTM w).tm.initCfg x) i =
      catalogPrefixCfg w x (some ⟨i, by omega⟩) 1 (w.take i) := by
  intro i
  induction i with
  | zero =>
    intro hi
    apply Cfg.ext_zero_tapes <;> simp [catalogPrefixCfg, prependTM]
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hlt : i < w.length := by omega
    simp only [MultiTapeTM.step, catalogPrefixCfg, prependTM, dif_pos hlt, Action.apply]
    apply Cfg.ext_zero_tapes
    · rfl
    · simp
    · rw [List.take_succ, List.getElem?_eq_getElem hlt]

/-- The copy phase emits one input bit per step and preserves the fixed prefix. -/
private lemma catalogPrefixTM_copy (w x : List Bool) : ∀ i (hi : i ≤ x.length),
    (prependTM w).tm.runFrom
      (catalogPrefixCfg w x (some ⟨w.length, by omega⟩) 1 w) i =
      catalogPrefixCfg w x (some ⟨w.length, by omega⟩) ⟨i + 1, by omega⟩
        (w ++ x.take i) := by
  intro i
  induction i with
  | zero => intro hi; simp [catalogPrefixCfg]
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hsym : (catalogPrefixCfg w x (some ⟨w.length, by omega⟩)
        ⟨i + 1, by omega⟩ (w ++ x.take i)).inputSymbol = some (x[i]'(by omega)) :=
      inputSymbolInner i (by simp only [catalogPrefixCfg]; omega) (by omega)
    change ((prependTM w).tm.tr ⟨w.length, by omega⟩
      (catalogPrefixCfg w x (some ⟨w.length, by omega⟩) ⟨i + 1, by omega⟩
        (w ++ x.take i)).inputSymbol _).apply _ = _
    rw [hsym]
    simp only [prependTM, Nat.lt_irrefl, ↓reduceDIte, Action.apply, catalogPrefixCfg]
    apply Cfg.ext_zero_tapes
    · rfl
    · change moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos = _
      rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
    · rw [List.take_succ, List.getElem?_eq_getElem (by omega), List.append_assoc]

/-- **The prepending machine's time**. The prepending machine computes `x ↦ w ++ x` within
`|w| + n + 1` steps.

**Proof sketch.** Today's proof: the emission chain writes `w` in `|w|` steps
(`catalogPrefixTM_emit`), the copy state copies the input in `|x|` more (`catalogPrefixTM_copy`),
and the blank after the input halts. -/
theorem prependTM_computes (w : List Bool) :
    (prependTM w).ComputesFunInTime (fun x => w ++ x) (fun n => w.length + n + 1) := by
  intro x
  apply (FinTM.computesInTime_iff _ _ _ _).mpr
  dsimp only
  rw [show w.length + x.length + 1 = w.length + (x.length + 1) by omega,
    MultiTapeTM.runFrom_add, catalogPrefixTM_emit w x w.length (Nat.le_refl _)]
  simp only [List.take_length]
  rw [MultiTapeTM.runFrom_succ_eq_step', catalogPrefixTM_copy w x x.length (Nat.le_refl _)]
  simp [prependTM, catalogPrefixCfg, MultiTapeTM.step, Cfg.inputSymbol, Fin.ext_iff, Action.apply]


/-- A zero-work-tape configuration indexed by the number of input bits passed. -/
private def scanCfg {S : Type} (x : List Bool) (q : Option S)
    (i : ℕ) (hi : i ≤ x.length) (out : List Bool) : Cfg 0 Bool S x :=
  ⟨q, ⟨i + 1, by omega⟩, fun j => j.elim0, fun j => j.elim0, out⟩

/-- Reading at the indexed input position returns the optional list entry. -/
private lemma scanCfg_read {S : Type} (x : List Bool) (q : Option S)
    (i : ℕ) (hi : i ≤ x.length) (out : List Bool) :
    (scanCfg x q i hi out).inputSymbol = x[i]? := by
  by_cases h : i < x.length
  · rw [List.getElem?_eq_getElem h]
    exact inputSymbolInner i (by simp [scanCfg]; omega) h
  · have he : i = x.length := by omega
    subst i
    simp [scanCfg, Cfg.inputSymbol, Fin.ext_iff]

/-- A copy state emits the next `j` input bits after an arbitrary output prefix.
**Proof sketch.** Induct on the number of copied cells; each transition appends
the scanned bit and moves right. The indexed configuration keeps the boundary
case separate from the actual bit-reading steps. -/
private lemma scanCopy_run {S : Type} (tm : MultiTapeTM 0 Bool S) (q : S)
    (htr : ∀ inp work, tm.tr q inp work = match inp with
      | some b => ⟨.pos, fun j => j.elim0, some b, some q⟩
      | none => ⟨0, fun j => j.elim0, none, none⟩)
    (x out : List Bool) : ∀ j (hj : j ≤ x.length),
    tm.runFrom (scanCfg x (some q) 0 (by omega) out) j =
      scanCfg x (some q) j hj (out ++ x.take j) := by
  intro j
  induction j with
  | zero => intro hj; simp [scanCfg]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    unfold MultiTapeTM.step
    change (tm.tr q (scanCfg x (some q) j (by omega) (out ++ x.take j)).inputSymbol
      _).apply _ = _
    rw [htr, scanCfg_read, List.getElem?_eq_getElem (by omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · exact moveInputPos_pos_of_ne_right _ (by simp [scanCfg]; omega)
    · simp only [Action.apply, scanCfg, Option.toList_some, List.take_succ,
        List.getElem?_eq_getElem (by omega : j < x.length), List.append_assoc]

/-- After copying the entire input, the right-blank transition halts silently. -/
private lemma scanCopy_finish {S : Type} (tm : MultiTapeTM 0 Bool S) (q : S)
    (htr : ∀ inp work, tm.tr q inp work = match inp with
      | some b => ⟨.pos, fun j => j.elim0, some b, some q⟩
      | none => ⟨0, fun j => j.elim0, none, none⟩)
    (x out : List Bool) :
    tm.runFrom (scanCfg x (some q) 0 (by omega) out) (x.length + 1) =
      scanCfg x none x.length (by omega) (out ++ x) := by
  rw [MultiTapeTM.runFrom_succ_eq_step', scanCopy_run tm q htr x out _ (by omega)]
  unfold MultiTapeTM.step
  change (tm.tr q (scanCfg x (some q) x.length (by omega)
    (out ++ x.take x.length)).inputSymbol _).apply _ = _
  rw [htr, scanCfg_read]
  apply Cfg.ext_zero_tapes <;> simp [Action.apply, scanCfg]

/-- Duplicate the input into the self-delimiting pair: double on the first
pass, rewind silently after emitting the separator's first bit, then emit its
second bit and copy. Every input is legal, so no validation buffer is needed. -/
private def pairDupTM : FinTM Bool where
  k := 0
  State := Fin 5
  tm :=
    { q₀ := 0
      tr := fun q inp _ => match q.val with
        | 0 => match inp with
          | some b => ⟨0, fun j => j.elim0, some b, some 1⟩
          | none => ⟨.neg, fun j => j.elim0, some false, some 2⟩
        | 1 => ⟨.pos, fun j => j.elim0, inp, some 0⟩
        | 2 => match inp with
          | some _ => controlAction .neg (some 2)
          | none => controlAction .pos (some 3)
        | 3 => ⟨0, fun j => j.elim0, some true, some 4⟩
        | _ => match inp with
          | some b => ⟨.pos, fun j => j.elim0, some b, some 4⟩
          | none => ⟨0, fun j => j.elim0, none, none⟩ }

/-- Every two first-pass transitions emit one doubled input bit.
**Proof sketch.** The first transition emits while staying at the scanned
cell, and the second emits that same bit and advances. Induction concatenates
these two-step blocks, leaving the right blank for the separator transition. -/
private lemma pairDup_double (x : List Bool) : ∀ j (hj : j ≤ x.length),
    pairDupTM.tm.runFrom (pairDupTM.tm.initCfg x) (2 * j) =
      scanCfg x (some (0 : Fin 5)) j hj ((x.take j).flatMap fun b => [b, b]) := by
  intro j
  induction j with
  | zero => intro hj; apply Cfg.ext_zero_tapes <;> simp [scanCfg, pairDupTM]
  | succ j ih =>
    intro hj
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hread := scanCfg_read x (some (0 : Fin 5)) j (by omega)
      ((x.take j).flatMap fun b => [b, b])
    rw [List.getElem?_eq_getElem (by omega)] at hread
    have hfirst : pairDupTM.tm.step
        (scanCfg x (some (0 : Fin 5)) j (by omega) ((x.take j).flatMap fun b => [b, b])) =
        scanCfg x (some (1 : Fin 5)) j (by omega)
          (((x.take j).flatMap fun b => [b, b]) ++ [x[j]'(by omega)]) := by
      unfold MultiTapeTM.step
      change (pairDupTM.tm.tr (0 : Fin 5) _ _).apply _ = _
      rw [hread]
      apply Cfg.ext_zero_tapes <;> simp [pairDupTM, Action.apply, scanCfg]
    rw [hfirst]
    unfold MultiTapeTM.step
    change (pairDupTM.tm.tr (1 : Fin 5) _ _).apply _ = _
    rw [scanCfg_read, List.getElem?_eq_getElem (by omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · exact moveInputPos_pos_of_ne_right _ (by simp [scanCfg]; omega)
    · change (((x.take j).flatMap fun b => [b, b]) ++ [x[j]'(by omega)]) ++
        [x[j]'(by omega)] = (x.take (j + 1)).flatMap fun b => [b, b]
      simp only [List.take_succ, List.getElem?_eq_getElem (by omega : j < x.length),
        Option.toList_some, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- The two passes and rewind take exactly `4|x|+4` transitions.
**Proof sketch.** Doubling costs `2|x|`, emitting the first separator bit
costs one, rewind and dispatch cost `|x|+1`, the second separator bit costs
one, and copying with its final blank test costs `|x|+1`. -/
private lemma pairDup_computes (x : List Bool) :
    pairDupTM.ComputesInTime x (pairEncode x x) (4 * (x.length + 1)) := by
  let pre := x.flatMap fun b => [b, b]
  let c : Cfg 0 Bool (Fin 5) x :=
    ⟨some 2, ⟨x.length, by omega⟩, fun j => j.elim0, fun j => j.elim0, pre ++ [false]⟩
  have hsep : pairDupTM.tm.step (scanCfg x (some (0 : Fin 5)) x.length (by omega) pre) = c := by
    unfold MultiTapeTM.step
    change (pairDupTM.tm.tr (0 : Fin 5) _ _).apply _ = _
    rw [scanCfg_read]
    apply Cfg.ext_zero_tapes
    · simp [pairDupTM, c]
    · simpa [pairDupTM, Action.apply, scanCfg, c] using
        moveInputPos_neg_of_ne_left (⟨x.length + 1, by omega⟩ : Fin (x.length + 2))
          (by simp [Fin.ext_iff])
    · simp [pairDupTM, Action.apply, scanCfg, c]
  have hr := rewind_scan pairDupTM.tm (2 : Fin 5) (some (3 : Fin 5)) (fun _ _ => rfl) c rfl (by simp [c])
  have hemit : pairDupTM.tm.step {c with state := some (3 : Fin 5), inputPos := 1} =
      scanCfg x (some (4 : Fin 5)) 0 (by omega) (pre ++ [false, true]) := by
    apply Cfg.ext_zero_tapes <;>
      simp [MultiTapeTM.step, pairDupTM, c, scanCfg, Action.apply, List.append_assoc]
  have h1 : pairDupTM.tm.runFrom (pairDupTM.tm.initCfg x) (2 * x.length + 1) = c := by
    rw [MultiTapeTM.runFrom_succ_eq_step', pairDup_double x x.length (by omega)]
    simpa only [List.take_length] using hsep
  have h2 : pairDupTM.tm.runFrom (pairDupTM.tm.initCfg x)
      (2 * x.length + 1 + (x.length + 1)) =
      {c with state := some (3 : Fin 5), inputPos := 1} := by
    rw [MultiTapeTM.runFrom_add, h1]
    exact hr
  have h3 : pairDupTM.tm.runFrom (pairDupTM.tm.initCfg x)
      (2 * x.length + 1 + (x.length + 1) + 1) =
      scanCfg x (some (4 : Fin 5)) 0 (by omega) (pre ++ [false, true]) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', h2, hemit]
  apply (computesInTime_iff _ _ _ _).mpr
  rw [show 4 * (x.length + 1) = (2 * x.length + 1 + (x.length + 1) + 1) +
    (x.length + 1) by omega, MultiTapeTM.runFrom_add, h3,
    scanCopy_finish pairDupTM.tm (4 : Fin 5) (fun _ _ => rfl)]
  exact ⟨rfl, rfl⟩

/-- Copy a suffix from an already-positioned input head, preserving prior output.
**Proof sketch.** Induct on the suffix. A nonempty suffix emits its first bit
and shifts the prefix/suffix boundary by one. The empty suffix reads the right
blank and halts without another emission. -/
private lemma scanCopy_suffix {S : Type} (tm : MultiTapeTM 0 Bool S) (q : S)
    (htr : ∀ inp work, tm.tr q inp work = match inp with
      | some b => ⟨.pos, fun j => j.elim0, some b, some q⟩
      | none => ⟨0, fun j => j.elim0, none, none⟩)
    (x rest : List Bool) : ∀ pre out (hx : x = pre ++ rest),
    tm.runFrom (scanCfg x (some q) pre.length (by simp [hx]) out) (rest.length + 1) =
      scanCfg x none x.length (by omega) (out ++ rest) := by
  induction rest with
  | nil =>
    intro pre out hx
    subst x
    simp only [List.length_nil, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (tm.tr q _ _).apply _ = _
    rw [htr, scanCfg_read]
    apply Cfg.ext_zero_tapes <;> simp [Action.apply, scanCfg]
  | cons b rest ih =>
    intro pre out hx
    have hlen : pre.length < x.length := by simp [hx]
    have hread : x[pre.length]? = some b := by simp [hx]
    have hs : tm.step (scanCfg x (some q) pre.length (by omega) out) =
        scanCfg x (some q) (pre ++ [b]).length (by simp [hx]) (out ++ [b]) := by
      unfold MultiTapeTM.step
      change (tm.tr q _ _).apply _ = _
      rw [htr, scanCfg_read, hread]
      apply Cfg.ext_zero_tapes
      · rfl
      · simpa [scanCfg] using moveInputPos_pos_of_ne_right
          (⟨pre.length + 1, by omega⟩ : Fin (x.length + 2)) (by simp; omega)
      · rfl
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [b]) (out ++ [b]) (by simpa [List.append_assoc] using hx)

/-- A true-prefix scan either remains silent or emits one false per true.
**Proof sketch.** Induct on the prefix length. Taking a shorter prefix gives
the induction hypothesis, and the last entry of the longer prefix identifies
the symbol read by the next transition. -/
private lemma scanTrues_run {S : Type} (tm : MultiTapeTM 0 Bool S) (q : S)
    (emit : Bool)
    (htr : ∀ work, tm.tr q (some true) work =
      ⟨.pos, fun j => j.elim0, if emit then some false else none, some q⟩)
    (x : List Bool) : ∀ j (hj : j ≤ x.length),
    x.take j = List.replicate j true →
    tm.runFrom (scanCfg x (some q) 0 (by omega) []) j =
      scanCfg x (some q) j hj (if emit then List.replicate j false else []) := by
  intro j
  induction j with
  | zero => intro hj hp; cases emit <;> rfl
  | succ j ih =>
    intro hj hp
    have hshort : x.take j = List.replicate j true := by
      have h := congrArg (List.take j) hp
      simpa only [List.take_take, List.take_replicate, Nat.min_eq_left (by omega : j ≤ j + 1)] using h
    have hb : x[j]? = some true := by
      have h := congrArg (fun w : List Bool => w[j]?) hp
      simpa [List.getElem?_take, Nat.lt_succ_self] using h
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega) hshort]
    unfold MultiTapeTM.step
    change (tm.tr q _ _).apply _ = _
    rw [scanCfg_read, hb, htr]
    apply Cfg.ext_zero_tapes
    · rfl
    · exact moveInputPos_pos_of_ne_right _ (by simp [scanCfg]; omega)
    · cases emit <;> simp [Action.apply, scanCfg, List.replicate_succ']

/-- Either every input bit is true (overflow), or its first false splits off
the carry prefix and determines the exact incremented word. -/
private lemma incFixed_cases (x : List Bool) :
    (x = List.replicate x.length true ∧ incFixed x = none) ∨
      ∃ j rest, x = List.replicate j true ++ false :: rest ∧
        incFixed x = some (List.replicate j false ++ true :: rest) := by
  induction x with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | cons b x ih =>
    cases b with
    | false => exact Or.inr ⟨0, x, rfl, rfl⟩
    | true =>
      rcases ih with ⟨hx, hinc⟩ | ⟨j, rest, hx, hinc⟩
      · exact Or.inl ⟨by simpa only [List.length_cons, List.replicate_succ, List.cons.injEq, true_and] using hx, by simp [incFixed, hinc]⟩
      · exact Or.inr ⟨j + 1, rest, by simp [hx, List.replicate_succ],
          by simp [incFixed, hinc, List.replicate_succ]⟩

/-- **The fixed-width incrementer**. A machine with no work tapes that first scans its input for a
`false` without emitting (an all-`true` word is the overflow, which halts with empty output),
rewinds, and then emits the little-endian fixed-width successor `Turing.incFixed x`: `false` over
the carry prefix, `true` at the first `false`, then the rest verbatim. -/
def incFixedTM : FinTM Bool where
  k := 0
  State := Fin 4
  tm :=
    { q₀ := 0
      tr := fun q inp _ => match q.val with
        | 0 => match inp with
          | some true => ⟨.pos, fun j => j.elim0, none, some 0⟩
          | some false => controlAction .neg (some 1)
          | none => controlAction 0 none
        | 1 => match inp with
          | some _ => controlAction .neg (some 1)
          | none => controlAction .pos (some 2)
        | 2 => match inp with
          | some true => ⟨.pos, fun j => j.elim0, some false, some 2⟩
          | some false => ⟨.pos, fun j => j.elim0, some true, some 3⟩
          | none => controlAction 0 none
        | _ => match inp with
          | some b => ⟨.pos, fun j => j.elim0, some b, some 3⟩
          | none => ⟨0, fun j => j.elim0, none, none⟩ }

/-- **The incrementer's time**. On every input the incrementer halts within `3·(|x| + 1)` steps with
output `(incFixed x).getD []`.

**Proof sketch.** Today's proof: the overflow scan, the rewind and the emitting pass each cost
at most `|x| + 1` steps, by the case split `incFixed_cases`. -/
theorem incFixedTM_computes (x : List Bool) :
    incFixedTM.ComputesInTime x ((incFixed x).getD []) (3 * (x.length + 1)) := by
  rcases incFixed_cases x with ⟨hx, hinc⟩ | ⟨j, rest, hx, hinc⟩
  · have hr := scanTrues_run incFixedTM.tm (0 : Fin 4) false (fun _ => rfl)
      x x.length (by omega) (by simpa using hx)
    have hh : incFixedTM.ComputesInTime x [] (x.length + 1) := by
      apply (computesInTime_iff _ _ _ _).mpr
      rw [MultiTapeTM.runFrom_succ_eq_step', show incFixedTM.tm.initCfg x =
        scanCfg x (some (0 : Fin 4)) 0 (by omega) [] from
          by apply Cfg.ext_zero_tapes <;> simp [incFixedTM, scanCfg], hr]
      unfold MultiTapeTM.step
      change ((incFixedTM.tm.tr (0 : Fin 4) _ _).apply _).state = none ∧ _
      rw [scanCfg_read]
      simp [incFixedTM, controlAction, Action.apply, scanCfg]
    simpa only [hinc, Option.getD_none] using hh.mono (by omega)
  · have hj : j < x.length := by simp [hx]
    have hpre : x.take j = List.replicate j true := by simp [hx]
    have hread : x[j]? = some false := by simp [hx]
    let c : Cfg 0 Bool (Fin 4) x :=
      ⟨some 1, ⟨j, by omega⟩, fun i => i.elim0, fun i => i.elim0, []⟩
    have hdet : incFixedTM.tm.runFrom (incFixedTM.tm.initCfg x) (j + 1) = c := by
      rw [MultiTapeTM.runFrom_succ_eq_step', show incFixedTM.tm.initCfg x =
        scanCfg x (some (0 : Fin 4)) 0 (by omega) [] from
          by apply Cfg.ext_zero_tapes <;> simp [incFixedTM, scanCfg],
        scanTrues_run incFixedTM.tm (0 : Fin 4) false (fun _ => rfl) x j (by omega) hpre]
      unfold MultiTapeTM.step
      change (incFixedTM.tm.tr (0 : Fin 4) _ _).apply _ = _
      rw [scanCfg_read, hread]
      apply Cfg.ext_zero_tapes
      · rfl
      · simpa [incFixedTM, controlAction, Action.apply, scanCfg, c] using
          moveInputPos_neg_of_ne_left (⟨j + 1, by omega⟩ : Fin (x.length + 2))
            (by simp [Fin.ext_iff])
      · rfl
    have hrew : incFixedTM.tm.runFrom (incFixedTM.tm.initCfg x) (j + 1 + (j + 1)) =
        scanCfg x (some (2 : Fin 4)) 0 (by omega) [] := by
      rw [MultiTapeTM.runFrom_add, hdet]
      exact rewind_scan incFixedTM.tm (1 : Fin 4) (some (2 : Fin 4))
        (fun _ _ => rfl) c rfl (by simp [c]; omega)
    have hemit : incFixedTM.tm.runFrom (scanCfg x (some (2 : Fin 4)) 0 (by omega) [])
        (j + 1) = scanCfg x (some (3 : Fin 4)) (j + 1) (by omega)
          (List.replicate j false ++ [true]) := by
      rw [MultiTapeTM.runFrom_succ_eq_step',
        scanTrues_run incFixedTM.tm (2 : Fin 4) true (fun _ => rfl) x j (by omega) hpre]
      unfold MultiTapeTM.step
      change (incFixedTM.tm.tr (2 : Fin 4) _ _).apply _ = _
      rw [scanCfg_read, hread]
      apply Cfg.ext_zero_tapes
      · rfl
      · exact moveInputPos_pos_of_ne_right _ (by simp [scanCfg]; omega)
      · rfl
    have hcopy := scanCopy_suffix incFixedTM.tm (3 : Fin 4) (fun _ _ => rfl)
      x rest (List.replicate j true ++ [false]) (List.replicate j false ++ [true])
      (by simpa [List.append_assoc] using hx)
    have hh : incFixedTM.ComputesInTime x (List.replicate j false ++ true :: rest)
        ((j + 1 + (j + 1)) + ((j + 1) + (rest.length + 1))) := by
      apply (computesInTime_iff _ _ _ _).mpr
      rw [MultiTapeTM.runFrom_add, hrew, MultiTapeTM.runFrom_add, hemit]
      simp only [List.length_append, List.length_replicate, List.length_singleton] at hcopy
      rw [hcopy]
      exact ⟨rfl, by simp [scanCfg, List.append_assoc]⟩
    have hlen : x.length = j + 1 + rest.length := by simp [hx]; omega
    simpa only [hinc, Option.getD_some] using hh.mono (by omega)

/-- A right-moving zero-tape transition advances the indexed configuration
and appends exactly its optional emission. -/
private lemma scanStep_right {S : Type} (tm : MultiTapeTM 0 Bool S)
    (x : List Bool) (q : S) (q' : Option S) (i : ℕ) (hi : i < x.length)
    (out : List Bool) (emit : Option Bool)
    (htr : ∀ work, tm.tr q x[i]? work = ⟨.pos, fun j => j.elim0, emit, q'⟩) :
    tm.step (scanCfg x (some q) i (by omega) out) =
      scanCfg x q' (i + 1) (by omega) (out ++ emit.toList) := by
  unfold MultiTapeTM.step
  change (tm.tr q _ _).apply _ = _
  rw [scanCfg_read, htr]
  apply Cfg.ext_zero_tapes
  · rfl
  · exact moveInputPos_pos_of_ne_right _ (by simp [scanCfg]; omega)
  · rfl

/-- **The pair-grammar validator**. A machine with no work tapes that scans aligned pairs of input
bits, remembering the first bit of the current pair, and emits the single verdict
`(pairDecode x).isSome` at the separator `false, true` or at the first malformed pair. -/
def pairValidTM : FinTM Bool where
  k := 0
  State := Option Bool
  tm :=
    { q₀ := none
      tr := fun q inp _ => match q, inp with
        | none, some b => ⟨.pos, fun j => j.elim0, none, some (some b)⟩
        | some b, some c =>
          if b = c then ⟨.pos, fun j => j.elim0, none, some none⟩
          else ⟨.pos, fun j => j.elim0, some (!b && c), none⟩
        | _, none => ⟨0, fun j => j.elim0, some false, none⟩ }

/-- One aligned block either continues silently or halts with its verdict. -/
private lemma pairValid_block (x pre rest : List Bool) (b c : Bool)
    (hx : x = pre ++ b :: c :: rest) :
    pairValidTM.tm.runFrom (scanCfg x (some none) pre.length (by simp [hx]) []) 2 =
      if b = c then scanCfg x (some none) (pre.length + 2) (by simp [hx]) []
      else scanCfg x none (pre.length + 2) (by simp [hx]) [!b && c] := by
  have h1 := scanStep_right pairValidTM.tm x none (some (some b)) pre.length
    (by simp [hx]) [] none (by intro work; simp [hx, pairValidTM])
  have h2 := scanStep_right pairValidTM.tm x (some b)
    (if b = c then some none else none) (pre.length + 1) (by simp [hx])
    [] (if b = c then none else some (!b && c)) (by
      intro work
      have hr : x[pre.length + 1]? = some c := by simp [hx]
      rw [hr]
      by_cases h : b = c <;> simp [pairValidTM, h])
  change pairValidTM.tm.step (pairValidTM.tm.step _) = _
  rw [h1]
  simp only [Option.toList_none, List.append_nil]
  rw [h2]
  by_cases h : b = c <;> simp [h]

/-- The validity scanner halts within one more than the unprocessed length.
**Proof sketch.** Induct in aligned two-bit blocks. The empty and singleton
cases fail on a boundary blank. Equal-bit blocks invoke the induction
hypothesis silently; `01` succeeds and `10` fails immediately, independently
of the suffix. Thus no verdict is emitted before validity is decided. -/
private lemma pairValid_run (x rest : List Bool) : ∀ pre (hx : x = pre ++ rest),
    ∃ t ≤ rest.length + 1,
      (pairValidTM.tm.runFrom
        (scanCfg x (some none) pre.length (by simp [hx]) []) t).state = none ∧
      (pairValidTM.tm.runFrom
        (scanCfg x (some none) pre.length (by simp [hx]) []) t).output =
          [(pairDecode rest).isSome] := by
  induction rest using List.twoStepInduction with
  | nil =>
    intro pre hx
    refine ⟨1, by simp, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((pairValidTM.tm.tr none _ _).apply _).state = none ∧ _
    rw [scanCfg_read]
    simp [hx, pairValidTM, Action.apply, scanCfg, pairDecode]
  | singleton b =>
    intro pre hx
    have h1 := scanStep_right pairValidTM.tm x none (some (some b)) pre.length
      (by simp [hx]) [] none (by intro work; simp [hx, pairValidTM])
    refine ⟨2, by simp, ?_⟩
    change (pairValidTM.tm.step (pairValidTM.tm.step _)).state = none ∧
      (pairValidTM.tm.step (pairValidTM.tm.step _)).output = _
    rw [h1]
    unfold MultiTapeTM.step
    change ((pairValidTM.tm.tr (some b) _ _).apply _).state = none ∧ _
    rw [scanCfg_read]
    cases b <;> simp [hx, pairValidTM, Action.apply, scanCfg, pairDecode]
  | cons_cons b c rest ih _ =>
    intro pre hx
    by_cases h : b = c
    · subst c
      obtain ⟨t, ht, hs, ho⟩ := ih (pre ++ [b, b]) (by simpa [List.append_assoc] using hx)
      refine ⟨2 + t, by simp only [List.length_cons] at *; omega, ?_⟩
      rw [MultiTapeTM.runFrom_add, pairValid_block x pre rest b b hx, if_pos rfl]
      simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
      refine ⟨hs, ?_⟩
      cases b <;> simpa [pairDecode] using ho
    · refine ⟨2, by simp, ?_⟩
      rw [pairValid_block x pre rest b c hx, if_neg h]
      cases b <;> cases c <;> simp_all [scanCfg, pairDecode]

/-- **The validator's time**. On every input the validator halts within `|x| + 1` steps with output
`[(pairDecode x).isSome]`.

**Proof sketch.** Today's proof: one step per input symbol (`pairValid_run`), and the verdict
is emitted on the halting transition. -/
theorem pairValidTM_computes (x : List Bool) :
    pairValidTM.ComputesInTime x [(pairDecode x).isSome] (x.length + 1) := by
  obtain ⟨t, ht, hs, ho⟩ := pairValid_run x x [] rfl
  have hinit : pairValidTM.tm.initCfg x = scanCfg x (some none) 0 (by omega) [] := by
    apply Cfg.ext_zero_tapes <;> simp [pairValidTM, scanCfg]
  have h : pairValidTM.ComputesInTime x [(pairDecode x).isSome] t := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [hinit]
    exact ⟨hs, ho⟩
  exact h.mono ht

/-- **The pair extractor**. On `pairEncode a b` it validates the doubled prefix while buffering `a`
on its single work tape, then emits `a` if `first` and the suffix `b` if `second`; on a malformed
input it halts with empty output. One machine serves the first-component, second-component and
concatenation rows. -/
def pairExtractTM (first second : Bool) : FinTM Bool where
  k := 1
  State := Option Bool ⊕ Fin 3
  tm :=
    { q₀ := .inl none
      tr := fun q inp work => match q with
        | .inl none => match inp with
          | some b => ⟨.pos, fun _ => (none, 0), none, some (.inl (some b))⟩
          | none => ⟨0, fun _ => (none, 0), none, none⟩
        | .inl (some b) => match inp with
          | none => ⟨0, fun _ => (none, 0), none, none⟩
          | some c =>
            if b = c then
              ⟨.pos, fun _ => (some (some b), .pos), none, some (.inl none)⟩
            else if b then ⟨.pos, fun _ => (none, 0), none, none⟩
            else ⟨.pos, fun _ => (none, .neg), none, some (.inr 0)⟩
        | .inr q => match q.val with
          | 0 => match work 0 with
            | some _ => ⟨0, fun _ => (none, .neg), none, some (.inr 0)⟩
            | none => ⟨0, fun _ => (none, .pos), none, some (.inr 1)⟩
          | 1 => match work 0 with
            | some b => ⟨0, fun _ => (none, .pos), if first then some b else none, some (.inr 1)⟩
            | none => ⟨0, fun _ => (none, 0), none, some (.inr 2)⟩
          | _ => if second then match inp with
              | some b => ⟨.pos, fun _ => (none, 0), some b, some (.inr 2)⟩
              | none => ⟨0, fun _ => (none, 0), none, none⟩
            else ⟨0, fun _ => (none, 0), none, none⟩ }

/-- The shared extractor's one-buffer configurations. -/
private def extractCfg (x : List Bool) (q : Option (Option Bool ⊕ Fin 3))
    (i : ℕ) (hi : i ≤ x.length) (a : List Bool) (z : ℤ) (out : List Bool) :
    Cfg 1 Bool (Option Bool ⊕ Fin 3) x :=
  ⟨q, ⟨i + 1, by omega⟩, fun _ => bufferTape a, fun _ => z, out⟩

/-- The extractor reads the indexed input entry independently of its buffer. -/
private lemma extractCfg_read (x : List Bool) (q : Option (Option Bool ⊕ Fin 3))
    (i : ℕ) (hi : i ≤ x.length) (a : List Bool) (z : ℤ) (out : List Bool) :
    (extractCfg x q i hi a z out).inputSymbol = x[i]? :=
  scanCfg_read x q i hi out

/-- Reading the first half of an aligned block preserves the buffer silently. -/
private lemma extract_first (first second : Bool) (x pre rest a : List Bool) (b : Bool)
    (hx : x = pre ++ b :: rest) :
    (pairExtractTM first second).tm.step
      (extractCfg x (some (.inl none)) pre.length (by simp [hx]) a a.length []) =
      extractCfg x (some (.inl (some b))) (pre.length + 1) (by simp [hx]) a a.length [] := by
  unfold MultiTapeTM.step
  change ((pairExtractTM first second).tm.tr (.inl none) _ _).apply _ = _
  rw [extractCfg_read]
  have hr : x[pre.length]? = some b := by simp [hx]
  rw [hr]
  refine Cfg.ext rfl ?_ rfl ?_ rfl
  · exact moveInputPos_pos_of_ne_right _ (by simp [extractCfg, hx])
  · funext i; simp [pairExtractTM, Action.apply, extractCfg]

/-- Equal-bit blocks append one decoded bit; `01` begins replay and `10`
halts silently. In particular, neither transition emits physical output. -/
private lemma extract_block (first second : Bool) (x pre rest a : List Bool) (b c : Bool)
    (hx : x = pre ++ b :: c :: rest) :
    (pairExtractTM first second).tm.runFrom
      (extractCfg x (some (.inl none)) pre.length (by simp [hx]) a a.length []) 2 =
      if b = c then extractCfg x (some (.inl none)) (pre.length + 2) (by simp [hx])
          (a ++ [b]) (a ++ [b]).length []
      else if b then extractCfg x none (pre.length + 2) (by simp [hx]) a a.length []
      else extractCfg x (some (.inr 0)) (pre.length + 2) (by simp [hx]) a (a.length - 1) [] := by
  change (pairExtractTM first second).tm.step ((pairExtractTM first second).tm.step _) = _
  rw [extract_first first second x pre (c :: rest) a b hx]
  unfold MultiTapeTM.step
  change ((pairExtractTM first second).tm.tr (.inl (some b)) _ _).apply _ = _
  rw [extractCfg_read]
  have hr : x[pre.length + 1]? = some c := by simp [hx]
  rw [hr]
  have hm : moveInputPos (⟨pre.length + 1 + 1, by simp [hx]⟩ : Fin (x.length + 2)) .pos =
      ⟨pre.length + 2 + 1, by simp [hx]; omega⟩ := by
    exact moveInputPos_pos_of_ne_right _ (by simp [hx])
  cases b <;> cases c <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
  all_goals refine Cfg.ext rfl hm ?_ ?_ rfl
  all_goals first
    | rfl
    | (funext i; exact (bufferTape_append a _).symm)
    | (funext i; simp [pairExtractTM, Action.apply, extractCfg])

/-- Rewinding the validated buffer from cell `j-1` takes `j+1` transitions.
**Proof sketch.** At the left blank, move right and enter replay. Otherwise
read a buffer cell, move left, and invoke the induction hypothesis. -/
private lemma extract_rewind (first second : Bool) (x a : List Bool)
    (i : ℕ) (hi : i ≤ x.length) : ∀ j, j ≤ a.length →
    (pairExtractTM first second).tm.runFrom
      (extractCfg x (some (.inr 0)) i hi a ((j : ℤ) - 1) []) (j + 1) =
      extractCfg x (some (.inr 1)) i hi a 0 [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    simp only [pairExtractTM, extractCfg, Cfg.workTapeSymbols, Nat.cast_zero,
      zero_sub, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext k; simp [Action.apply]
  | succ j ih =>
    intro hj
    have hs : (pairExtractTM first second).tm.step
        (extractCfg x (some (.inr 0)) i hi a (((j + 1 : ℕ) : ℤ) - 1) []) =
        extractCfg x (some (.inr 0)) i hi a ((j : ℤ) - 1) [] := by
      have hz : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [hz]
      unfold MultiTapeTM.step
      simp only [pairExtractTM, extractCfg, Cfg.workTapeSymbols, bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < a.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext k; simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Replay reads the buffered word once; the first-component flag decides
whether those reads emit. At the right blank the controller starts the suffix.
**Proof sketch.** Induct on the number of replayed cells. Each live step
preserves the tape and appends either its bit or nothing. -/
private lemma extract_replay (first second : Bool) (x a : List Bool)
    (i : ℕ) (hi : i ≤ x.length) : ∀ j (_hj : j ≤ a.length),
    (pairExtractTM first second).tm.runFrom
      (extractCfg x (some (.inr 1)) i hi a 0 []) j =
      extractCfg x (some (.inr 1)) i hi a j (if first then a.take j else []) := by
  intro j
  induction j with
  | zero => intro hj; cases first <;> rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    unfold MultiTapeTM.step
    simp only [pairExtractTM, extractCfg, Cfg.workTapeSymbols, bufferTape_nat,
      List.getElem?_eq_getElem (by omega : j < a.length)]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
    · funext k; simp [Action.apply]
    · change (if first then a.take j else []) ++
        (if first then some (a[j]'(by omega)) else none).toList =
          (if first then a.take (j + 1) else [])
      have ht : a.take j ++ [a[j]'(by omega)] = a.take (j + 1) := by
        rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
        rfl
      cases first with
      | false => rfl
      | true => exact ht

/-- Replay's right-blank test dispatches to the suffix state silently. -/
private lemma extract_replay_finish (first second : Bool) (x a : List Bool)
    (i : ℕ) (hi : i ≤ x.length) :
    (pairExtractTM first second).tm.runFrom
      (extractCfg x (some (.inr 1)) i hi a 0 []) (a.length + 1) =
      extractCfg x (some (.inr 2)) i hi a a.length (if first then a else []) := by
  rw [MultiTapeTM.runFrom_succ_eq_step', extract_replay first second x a i hi _ (by omega)]
  unfold MultiTapeTM.step
  simp only [pairExtractTM, extractCfg, Cfg.workTapeSymbols, bufferTape_nat,
    List.getElem?_length, List.take_length]
  refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
  · funext k; simp [Action.apply]
  · simp [Action.apply]

/-- With suffix copying enabled, the final phase emits the remaining input.
**Proof sketch.** The input prefix grows by one at each emitting transition;
the buffer and its head remain fixed. A right-blank test supplies the final
halting step. This is the one-buffer version of the private suffix-copy lemma. -/
private lemma extract_suffix (first : Bool) (x rest a : List Bool) :
    ∀ pre out (hx : x = pre ++ rest),
    (pairExtractTM first true).tm.runFrom
      (extractCfg x (some (.inr 2)) pre.length (by simp [hx]) a a.length out)
        (rest.length + 1) =
      extractCfg x none x.length (by omega) a a.length (out ++ rest) := by
  induction rest with
  | nil =>
    intro pre out hx
    simp only [List.length_nil, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((pairExtractTM first true).tm.tr (.inr 2) _ _).apply _ = _
    rw [extractCfg_read]
    have hr : x[pre.length]? = none := by simp [hx]
    rw [hr]
    refine Cfg.ext rfl ?_ rfl ?_ ?_
    · simp [pairExtractTM, Action.apply, extractCfg, hx]
    · funext k; simp [pairExtractTM, Action.apply, extractCfg]
    · simp [pairExtractTM, Action.apply, extractCfg]
  | cons b rest ih =>
    intro pre out hx
    have hs : (pairExtractTM first true).tm.step
        (extractCfg x (some (.inr 2)) pre.length (by simp [hx]) a a.length out) =
        extractCfg x (some (.inr 2)) (pre ++ [b]).length (by simp [hx])
          a a.length (out ++ [b]) := by
      unfold MultiTapeTM.step
      change ((pairExtractTM first true).tm.tr (.inr 2) _ _).apply _ = _
      rw [extractCfg_read]
      have hr : x[pre.length]? = some b := by simp [hx]
      rw [hr]
      refine Cfg.ext rfl ?_ rfl ?_ rfl
      · simpa [extractCfg] using moveInputPos_pos_of_ne_right
          (⟨pre.length + 1, by simp [hx]; omega⟩ : Fin (x.length + 2)) (by simp [hx])
      · funext k; simp [pairExtractTM, Action.apply, extractCfg]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [b]) (out ++ [b]) (by simpa [List.append_assoc] using hx)

/-- Once validation succeeds, rewind, replay, and optional suffix copying
cost at most `2|a|+|rest|+3` steps.
**Proof sketch.** The rewind costs `|a|+1`, and replay plus dispatch costs
`|a|+1`. Disabled suffix copying halts in one step; enabled copying uses
`|rest|+1`. Only these postvalidation phases emit output. -/
private lemma extract_finish (first second : Bool) (x pre rest a : List Bool)
    (hx : x = pre ++ rest) :
    ∃ t ≤ 2 * a.length + rest.length + 3,
      ((pairExtractTM first second).tm.runFrom
        (extractCfg x (some (.inr 0)) pre.length (by simp [hx]) a (a.length - 1) []) t).state = none ∧
      ((pairExtractTM first second).tm.runFrom
        (extractCfg x (some (.inr 0)) pre.length (by simp [hx]) a (a.length - 1) []) t).output =
          (if first then a else []) ++ (if second then rest else []) := by
  have hp : (pairExtractTM first second).tm.runFrom
      (extractCfg x (some (.inr 0)) pre.length (by simp [hx]) a (a.length - 1) [])
        ((a.length + 1) + (a.length + 1)) =
      extractCfg x (some (.inr 2)) pre.length (by simp [hx]) a a.length (if first then a else []) := by
    rw [MultiTapeTM.runFrom_add, extract_rewind first second x a _ _ _ (by omega),
      extract_replay_finish]
  cases second with
  | false =>
    refine ⟨(a.length + 1) + (a.length + 1) + 1, by omega, ?_⟩
    rw [MultiTapeTM.runFrom_succ_eq_step', hp]
    simp [MultiTapeTM.step, pairExtractTM, extractCfg, Action.apply]
  | true =>
    refine ⟨((a.length + 1) + (a.length + 1)) + (rest.length + 1), by omega, ?_⟩
    rw [MultiTapeTM.runFrom_add, hp, extract_suffix first x rest a pre _ hx]
    exact ⟨rfl, rfl⟩

/-- The silent aligned parser either rejects or validates and invokes replay.
**Proof sketch.** Induct over aligned two-bit blocks while carrying the
already-decoded buffer. A doubled bit costs two steps and enlarges the buffer
by one; the linear potential `3|rest|+2|a|+5` pays for both effects. Missing
and forbidden separators halt silently. At `01`, apply the validated finish
ledger. The result includes the previously buffered prefix only on success. -/
private lemma extract_run (first second : Bool) (x rest : List Bool) :
    ∀ pre a (hx : x = pre ++ rest),
    ∃ t ≤ 3 * rest.length + 2 * a.length + 5,
      ((pairExtractTM first second).tm.runFrom
        (extractCfg x (some (.inl none)) pre.length (by simp [hx]) a a.length []) t).state = none ∧
      ((pairExtractTM first second).tm.runFrom
        (extractCfg x (some (.inl none)) pre.length (by simp [hx]) a a.length []) t).output =
          match pairDecode rest with
          | some (b, c) => (if first then a ++ b else []) ++ (if second then c else [])
          | none => [] := by
  induction rest using List.twoStepInduction with
  | nil =>
    intro pre a hx
    refine ⟨1, by omega, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (((pairExtractTM first second).tm.tr (.inl none) _ _).apply _).state = none ∧ _
    rw [extractCfg_read]
    simp [hx, pairExtractTM, Action.apply, extractCfg, pairDecode]
  | singleton b =>
    intro pre a hx
    refine ⟨2, by simp, ?_⟩
    change ((pairExtractTM first second).tm.step ((pairExtractTM first second).tm.step _)).state = none ∧
      ((pairExtractTM first second).tm.step ((pairExtractTM first second).tm.step _)).output = _
    rw [extract_first first second x pre [] a b hx]
    unfold MultiTapeTM.step
    change (((pairExtractTM first second).tm.tr (.inl (some b)) _ _).apply _).state = none ∧ _
    rw [extractCfg_read]
    cases b <;> simp [hx, pairExtractTM, Action.apply, extractCfg, pairDecode]
  | cons_cons b c rest ih _ =>
    intro pre a hx
    by_cases h : b = c
    · subst c
      obtain ⟨t, ht, hs, ho⟩ := ih (pre ++ [b, b]) (a ++ [b]) (by simpa [List.append_assoc] using hx)
      refine ⟨2 + t, by simp only [List.length_append, List.length_cons, List.length_nil] at *; omega, ?_⟩
      rw [MultiTapeTM.runFrom_add, extract_block first second x pre rest a b b hx, if_pos rfl]
      simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
      refine ⟨?_, ?_⟩
      · simpa only [List.length_append, List.length_cons, List.length_nil] using hs
      · cases b <;> cases hd : pairDecode rest with
        | none => simpa [pairDecode, hd] using ho
        | some p => cases p; simpa [pairDecode, hd, List.append_assoc] using ho
    · cases b <;> cases c
      · exact False.elim (h rfl)
      · obtain ⟨t, ht, hs, ho⟩ := extract_finish first second x (pre ++ [false, true]) rest a
          (by simpa [List.append_assoc] using hx)
        refine ⟨2 + t, by simp only [List.length_cons]; omega, ?_⟩
        rw [MultiTapeTM.runFrom_add, extract_block first second x pre rest a false true hx]
        simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
        exact ⟨hs, by simpa [pairDecode] using ho⟩
      · refine ⟨2, by simp, ?_⟩
        rw [extract_block first second x pre rest a true false hx]
        simp [extractCfg, pairDecode]
      · exact False.elim (h rfl)

/-- **The extractor's time**. On every input the extractor halts within `5·(|x| + 1)` steps; its
output is the selected components of the decoded pair, and empty when the input is not a pair
encoding.

**Proof sketch.** Today's proof: the aligned scan reads the doubled prefix two cells at a time
while buffering, the separator turns it into a rewind of the buffer, the replay emits `a`, and
the suffix copy emits `b`; each phase is linear in `|x|` (`extract_run`). -/
theorem pairExtractTM_computes (first second : Bool) (x : List Bool) :
    (pairExtractTM first second).ComputesInTime x
      (match pairDecode x with
        | some (a, b) => (if first then a else []) ++ (if second then b else [])
        | none => []) (5 * (x.length + 1)) := by
  obtain ⟨t, ht, hs, ho⟩ := extract_run first second x x [] [] rfl
  have hinit : (pairExtractTM first second).tm.initCfg x =
      extractCfg x (some (.inl none)) 0 (by omega) [] 0 [] := by
    apply Cfg.ext <;> simp [pairExtractTM, extractCfg, MultiTapeTM.initCfg, Cfg.init]
  have hh : (pairExtractTM first second).ComputesInTime x
      (match pairDecode x with
        | some (a, b) => (if first then a else []) ++ (if second then b else [])
        | none => []) t := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [hinit]
    exact ⟨hs, by simpa using ho⟩
  exact hh.mono (by simp only [List.length_nil] at ht; omega)

/-- **First component**. The extractor at `(true, false)` computes the first component of a decoded
pair, and `[]` on a malformed input, within `5·(n + 1)` steps.

**Proof sketch.** Specialize `pairExtractTM_computes` and split on the decoding. -/
theorem pairExtractTM_fst :
    (pairExtractTM true false).ComputesFunInTime
      (fun x => ((pairDecode x).map Prod.fst).getD []) (fun n => 5 * (n + 1)) := by
  intro x
  have h := pairExtractTM_computes true false x
  cases hd : pairDecode x with
  | none => simpa [hd] using h
  | some p => cases p; simpa [hd] using h

/-- **Second component**. The extractor at `(false, true)` computes the second component of a
decoded pair, and `[]` on a malformed input, within `5·(n + 1)` steps.

**Proof sketch.** Specialize `pairExtractTM_computes` and split on the decoding. -/
theorem pairExtractTM_snd :
    (pairExtractTM false true).ComputesFunInTime
      (fun x => ((pairDecode x).map Prod.snd).getD []) (fun n => 5 * (n + 1)) := by
  intro x
  have h := pairExtractTM_computes false true x
  cases hd : pairDecode x with
  | none => simpa [hd] using h
  | some p => cases p; simpa [hd] using h

/-- **Concatenation of the components**. The extractor at `(true, true)` maps `pairEncode a b` to
`a ++ b`, and a malformed input to `[]`, within `5·(n + 1)` steps.

**Proof sketch.** Specialize `pairExtractTM_computes` and split on the decoding. -/
theorem pairExtractTM_concat :
    (pairExtractTM true true).ComputesFunInTime
      (fun z => match pairDecode z with
        | some (a, b) => a ++ b
        | none => []) (fun n => 5 * (n + 1)) := by
  intro x
  have h := pairExtractTM_computes true true x
  cases hd : pairDecode x with
  | none => simpa [hd] using h
  | some p => cases p; simpa [hd] using h

/-! ### The first-component extractor's complete run -/

/-- Re-indexing an extractor configuration along equal indices. -/
private lemma extractCfg_congr (x : List Bool) (q : Option (Option Bool ⊕ Fin 3))
    {i j : ℕ} (hi : i ≤ x.length) (hj : j ≤ x.length) (hij : i = j) {a a' : List Bool}
    (ha : a = a') {z z' : ℤ} (hz : z = z') (out : List Bool) :
    extractCfg x q i hi a z out = extractCfg x q j hj a' z' out := by
  subst hij ha hz; rfl

/-- The aligned scan buffers a doubled word silently, two steps per bit. -/
private lemma extract_scan (first second : Bool) (x rest : List Bool) :
    ∀ (w pre a : List Bool) (hx : x = pre ++ dbl w ++ rest),
    (pairExtractTM first second).tm.runFrom
      (extractCfg x (some (.inl none)) pre.length (by simp [hx]) a a.length []) (2 * w.length) =
      extractCfg x (some (.inl none)) (pre.length + 2 * w.length)
        (by simp [hx]) (a ++ w) (a ++ w).length [] := by
  intro w
  induction w with
  | nil =>
    intro pre a hx
    simp only [List.length_nil, Nat.mul_zero, MultiTapeTM.runFrom_zero]
    exact extractCfg_congr _ _ _ _ (by omega) (by simp) (by simp) _
  | cons b w ih =>
    intro pre a hx
    have hx' : x = pre ++ b :: b :: (dbl w ++ rest) := by simp [hx]
    have h1 := extract_block first second x pre (dbl w ++ rest) a b b hx'
    rw [if_pos rfl] at h1
    have h2 := ih (pre ++ [b, b]) (a ++ [b]) (by simp [hx])
    have e : 2 * (b :: w).length = 2 + 2 * w.length := by simp; ring
    simp only [e]
    rw [MultiTapeTM.runFrom_add, h1]
    rw [extractCfg_congr x (some (.inl none)) _ (by simp [hx])
      (by simp : pre.length + 2 = (pre ++ [b, b]).length) rfl rfl []]
    rw [h2]
    exact extractCfg_congr _ _ _ _ (by simp; omega) (by simp) (by simp) _

/-- **The first-component extractor's complete run.** On
`pairEncode a b` the extractor `pairExtractTM true false` first halts after exactly
`4·|a| + 5` steps, with output `a`, its input head on cell `2·|a| + 3` (just past the
separator), and its single work tape holding `a` as a buffer with the head one past it.

**Proof sketch.** The aligned scan buffers `a` in `2·|a|` steps; the separator block `01`
starts the rewind (two steps); rewinding and replaying cost `(|a| + 1) + (|a| + 1)` steps;
the suffix flag is off, so one silent stationary step halts. Liveness before the halt is
`runFrom_state_ne_none_of_le` at the replay's last configuration. -/
theorem pairExtractTM_fst_run (a b : List Bool) :
    (pairExtractTM true false).tm.runFrom
        ((pairExtractTM true false).tm.initCfg (pairEncode a b)) (4 * a.length + 5) =
      ⟨none, ⟨2 * a.length + 3, by simp [length_pairEncode]; omega⟩,
        fun _ => bufferTape a, fun _ => (a.length : ℤ), a⟩ ∧
    ∀ u < 4 * a.length + 5, ((pairExtractTM true false).tm.runFrom
        ((pairExtractTM true false).tm.initCfg (pairEncode a b)) u).state ≠ none := by
  set x := pairEncode a b with hxdef
  have hx0 : x = [] ++ dbl a ++ (false :: true :: b) := by simp [hxdef, pairEncode_eq_dbl]
  have hlen : (dbl a).length + 2 ≤ x.length := by simp [hxdef, length_pairEncode]
  have hinit : (pairExtractTM true false).tm.initCfg x =
      extractCfg x (some (.inl none)) ([] : List Bool).length (by simp)
        ([] : List Bool) ([] : List Bool).length [] := by
    rw [MultiTapeTM.initCfg_eq]
    apply Cfg.ext
    · rw [Cfg.init_state]; rfl
    · rw [Cfg.init_inputPos]; exact Fin.ext (by simp [extractCfg])
    · funext j p; rw [Cfg.init_workTapes]; simp [extractCfg]
    · funext j; rw [Cfg.init_workTapePos]; rfl
    · rw [Cfg.init_output]; rfl
  have hscan := extract_scan true false x (false :: true :: b) a [] [] hx0
  have hsep := extract_block true false x (dbl a) b a false true
    (by simp [hxdef, pairEncode_eq_dbl])
  simp only [Bool.false_eq_true, ↓reduceIte] at hsep
  have hp : (pairExtractTM true false).tm.runFrom
      (extractCfg x (some (.inr 0)) ((dbl a).length + 2) (by omega)
        a ((a.length : ℤ) - 1) []) ((a.length + 1) + (a.length + 1)) =
      extractCfg x (some (.inr 2)) ((dbl a).length + 2) (by omega)
        a a.length a := by
    rw [MultiTapeTM.runFrom_add, extract_rewind true false x a _ _ _ (by omega),
      extract_replay_finish]
    rfl
  have hlast : (pairExtractTM true false).tm.step
      (extractCfg x (some (.inr 2)) ((dbl a).length + 2) (by omega)
        a a.length a) =
      extractCfg x none ((dbl a).length + 2) (by omega) a a.length a := by
    rw [MultiTapeTM.step_of_some rfl]
    simp only [pairExtractTM, ↓reduceIte, Bool.false_eq_true]
    apply Cfg.ext
    · rw [Action.apply_state]; rfl
    · rw [Action.apply_inputPos]; exact moveInputPos_zero _
    · funext k
      rw [Action.apply_workTapes, Option.getD_none, Cfg.workTapeSymbols_eq, Function.update_eq_self]
      rfl
    · funext k; rw [Action.apply_workTapePos]; simp [extractCfg]
    · rw [Action.apply_output, Option.toList_none, List.append_nil]; rfl
  have hmid : (pairExtractTM true false).tm.runFrom
      ((pairExtractTM true false).tm.initCfg x)
        (2 * a.length + 2 + ((a.length + 1) + (a.length + 1))) =
      extractCfg x (some (.inr 2)) ((dbl a).length + 2) (by omega)
        a a.length a := by
    have hA : (pairExtractTM true false).tm.runFrom
        ((pairExtractTM true false).tm.initCfg x) (2 * a.length) =
        extractCfg x (some (.inl none)) (dbl a).length (by omega)
          a a.length [] := by
      rw [hinit, hscan]
      exact extractCfg_congr _ _ _ _ (by simp) (by simp) (by simp) _
    rw [MultiTapeTM.runFrom_add _ (2 * a.length + 2), MultiTapeTM.runFrom_add _ (2 * a.length) 2,
      hA, hsep]
    exact hp
  have htot : 4 * a.length + 5 = (2 * a.length + 2 + ((a.length + 1) + (a.length + 1))) + 1 := by
    ring
  refine ⟨?_, ?_⟩
  · rw [htot, MultiTapeTM.runFrom_succ_eq_step', hmid, hlast]
    refine Cfg.ext rfl ?_ rfl rfl rfl
    simp [extractCfg]
  · intro u hu
    refine MultiTapeTM.runFrom_state_ne_none_of_le _ _
      (2 * a.length + 2 + ((a.length + 1) + (a.length + 1)))
      ?_ u (by omega)
    rw [hmid]
    simp [extractCfg]

/-- **The extractor's run at its published budget**, as a corollary of the exact form: at the
extractor's published time budget `5·(|z| + 1)` the run has halted in the
complete configuration. -/
theorem pairExtractTM_fst_run_budget (a b : List Bool) :
    let M := pairExtractTM true false
    let d := M.tm.runFrom (M.tm.initCfg (pairEncode a b)) (5 * ((pairEncode a b).length + 1))
    d.state = none ∧ d.output = a ∧ d.inputPos.val = 2 * a.length + 3 ∧
      ∀ j : Fin M.k, d.workTapes j = bufferTape a ∧ d.workTapePos j = (a.length : ℤ) := by
  intro M d
  obtain ⟨h, -⟩ := pairExtractTM_fst_run a b
  have hle : 4 * a.length + 5 ≤ 5 * ((pairEncode a b).length + 1) := by
    rw [length_pairEncode]; omega
  have hd : d = M.tm.runFrom (M.tm.initCfg (pairEncode a b)) (4 * a.length + 5) := by
    change M.tm.runFrom _ _ = _
    rw [← Nat.add_sub_of_le hle, MultiTapeTM.runFrom_add, h, MultiTapeTM.runFrom_of_halt _ rfl]
  rw [hd, h]
  exact ⟨rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩

/-! The unary polynomial generator below is adapted privately from
`ClassNP/TMSAT.lean`, including its exact loop-depth ledger. -/

/-- Control for copying the side length, nested unary loops, and constant emission. -/
private inductive CatalogPolyControl (c C : ℕ) where
  | copy | setup
  | loop (i : Fin (c + 1))
  | rewind (i : Fin (c + 1))
  | advance (i : Fin (c + 2))
  | emit (j : Fin (C + 1))

/-- Enumerate the control through a finite sum representation, privately. -/
private instance catalogPolyControlFintype (c C : ℕ) : Fintype (CatalogPolyControl c C) :=
  derive_fintype% _

/-- Compare control states through the same finite sum representation, privately. -/
private instance catalogPolyControlDecidableEq (c C : ℕ) : DecidableEq (CatalogPolyControl c C) :=
  (proxy_equiv% (CatalogPolyControl c C)).symm.decidableEq

/-- A unary word of length `q`, surrounded by blanks. -/
private def catalogPolyTape (q : ℕ) (z : ℤ) : Option Bool :=
  if 0 ≤ z ∧ z < q then some true else none

/-- Move just the selected work head, preserving every tape. -/
private def catalogPolyMove {c C : ℕ} (i : Fin (c + 1)) (d : SignType)
    (s : CatalogPolyControl c C) : Action (c + 1) Bool (CatalogPolyControl c C) :=
  ⟨0, fun j => (none, if j = i then d else 0), none, some s⟩

/-- Finite machine emitting `C` symbols at each point of a `(c+1)`-dimensional
box. The unary loop tapes are copied in parallel; rewinding a completed inner
loop costs its side length, charged to the iterations that just completed. -/
private def catalogPolyUnaryTM (c C : ℕ) : FinTM Bool where
  k := c + 1
  State := CatalogPolyControl c C
  tm := {
    q₀ := .copy
    tr := fun s inp w => match s with
      | .copy => match inp with
        | some _ => ⟨.pos, fun _ => (some (some true), .pos), none, some .copy⟩
        | none => ⟨0, fun _ => (some (some true), .neg), none, some .setup⟩
      | .setup =>
        if w 0 = none then
          ⟨0, fun _ => (none, .pos), none, some (.loop (Fin.last c))⟩
        else ⟨0, fun _ => (none, .neg), none, some .setup⟩
      | .loop i =>
        if w i = none then catalogPolyMove i .neg (.rewind i)
        else ⟨0, fun _ => (none, 0), none,
          some (if h : i.val = 0 then .emit ⟨C, Nat.lt_succ_self C⟩
            else .loop ⟨i.val - 1, by omega⟩)⟩
      | .rewind i =>
        if w i = none then catalogPolyMove i .pos (.advance ⟨i.val + 1, by omega⟩)
        else catalogPolyMove i .neg (.rewind i)
      | .advance i =>
        if h : i.val < c + 1 then catalogPolyMove ⟨i.val, h⟩ .pos (.loop ⟨i.val, h⟩)
        else ⟨0, fun _ => (none, 0), none, none⟩
      | .emit j =>
        if h : j.val = 0 then ⟨0, fun _ => (none, 0), none, some (.advance 0)⟩
        else ⟨0, fun _ => (none, 0), some true,
          some (.emit ⟨j.val - 1, by omega⟩)⟩ }

/-- **The unary polynomial generator**. The machine that writes `C·(|x| + 1)^e` ones: for `e = 0`
the constant machine of `List.replicate C true`, and for `e = d + 1` the private engine with `d + 1`
nested unary loop tapes of side `|x| + 1`, installed by one input scan, which emits `C` ones at each
point of the box. -/
def polyUnaryTM (C : ℕ) : ℕ → FinTM Bool
  | 0 => constTM (List.replicate C true)
  | d + 1 => catalogPolyUnaryTM d C

/-- **The binary polynomial evaluator**. The machine computing `x ↦ Nat.bits (C·(|x| + 1)^e)`: the
constant machine of the answer when `C = 0` or `e = 0`, and otherwise the unary generator buffered
into the binary length counter. The split avoids the generator's linear banks where the answer is a
constant (round-1 finding 5 of the space rows). -/
def polyBitsTM (C e : ℕ) : FinTM Bool :=
  if C = 0 then constTM (Nat.bits 0) else
    match e with
    | 0 => constTM (Nat.bits C)
    | d + 1 => bufferedCompTM (polyUnaryTM C (d + 1)) lengthBitsTM

/-- A loop configuration, with all unary tapes installed and arbitrary head positions. -/
private def catalogPolyCfg {c C : ℕ} (x : List Bool) (q : ℕ)
    (s : CatalogPolyControl c C) (h : Fin (c + 1) → ℤ) (o : List Bool) :
    Cfg (c + 1) Bool (CatalogPolyControl c C) x :=
  ⟨some s, ⟨x.length + 1, by omega⟩, fun _ => catalogPolyTape q, h, o⟩

/-- Applying a head-only action updates exactly the selected head. -/
private lemma catalogPolyMove_apply {c C : ℕ} (x : List Bool) (q : ℕ)
    (s s' : CatalogPolyControl c C) (h : Fin (c + 1) → ℤ) (o : List Bool)
    (i : Fin (c + 1)) (d : SignType) :
    (catalogPolyMove i d s').apply (catalogPolyCfg x q s h o) =
      catalogPolyCfg x q s' (Function.update h i (h i + d.cast)) o := by
  apply Cfg.ext
  · rfl
  · exact moveInputPos_zero _
  · rfl
  · funext j
    by_cases hj : j = i <;> simp [catalogPolyMove, catalogPolyCfg, Action.apply, hj]
  · simp [catalogPolyMove, catalogPolyCfg, Action.apply]

/-- The finite emission chain appends exactly its remaining number of true bits. -/
private lemma catalogPoly_emit {c C : ℕ} (x : List Bool) (q : ℕ)
    (h : Fin (c + 1) → ℤ) : ∀ j (hj : j ≤ C) (o : List Bool),
    (catalogPolyUnaryTM c C).tm.runFrom
      (catalogPolyCfg x q (.emit ⟨j, by omega⟩) h o) (j + 1) =
      catalogPolyCfg x q (.advance 0) h (o ++ List.replicate j true) := by
  intro j
  induction j with
  | zero =>
    intro hj o
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;> simp [MultiTapeTM.step, catalogPolyUnaryTM, catalogPolyCfg, Action.apply]
  | succ j ih =>
    intro hj o
    have hs : (catalogPolyUnaryTM c C).tm.step
        (catalogPolyCfg x q (.emit ⟨j + 1, by omega⟩) h o) =
        catalogPolyCfg x q (.emit ⟨j, by omega⟩) h (o ++ [true]) := by
      apply Cfg.ext <;> simp [MultiTapeTM.step, catalogPolyUnaryTM, catalogPolyCfg, Action.apply]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs, ih (by omega)]
    simp [List.replicate_succ, List.append_assoc]

/-- Rewinding crosses a unary prefix and its left boundary, restoring head zero.
The other loop heads and the accumulated output remain unchanged. -/
private lemma catalogPoly_rewind {c C : ℕ} (x : List Bool) (q : ℕ)
    (h : Fin (c + 1) → ℤ) (o : List Bool) (i : Fin (c + 1)) :
    ∀ j (_hj : j ≤ q),
    (catalogPolyUnaryTM c C).tm.runFrom
      (catalogPolyCfg x q (.rewind i) (Function.update h i ((j : ℤ) - 1)) o) (j + 1) =
      catalogPolyCfg x q (.advance ⟨i.val + 1, by omega⟩) (Function.update h i 0) o := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change ((if _ then _ else _) : Action (c + 1) Bool (CatalogPolyControl c C)).apply _ = _
    simp only [Cfg.workTapeSymbols, catalogPolyCfg, Function.update_self,
      Nat.cast_zero, zero_sub, catalogPolyTape, show ¬(0 ≤ (-1 : ℤ) ∧ (-1 : ℤ) < q) by omega,
      ↓reduceIte]
    simpa [catalogPolyCfg] using catalogPolyMove_apply x q (.rewind i)
      (.advance ⟨i.val + 1, by omega⟩) (Function.update h i (-1)) o i .pos
  | succ j ih =>
    intro hj
    have hs : (catalogPolyUnaryTM c C).tm.step
        (catalogPolyCfg x q (.rewind i) (Function.update h i ((j + 1 : ℕ) - 1 : ℤ)) o) =
        catalogPolyCfg x q (.rewind i) (Function.update h i ((j : ℤ) - 1)) o := by
      change ((if _ then _ else _) : Action (c + 1) Bool (CatalogPolyControl c C)).apply _ = _
      simp only [Cfg.workTapeSymbols, catalogPolyCfg, Function.update_self,
        Nat.cast_add, Nat.cast_one, add_sub_cancel_right, catalogPolyTape,
        if_pos (show 0 ≤ (j : ℤ) ∧ (j : ℤ) < q by omega),
        reduceCtorEq, ↓reduceIte]
      simpa [catalogPolyCfg, sub_eq_add_neg] using catalogPolyMove_apply x q (.rewind i)
        (.rewind i) (Function.update h i (j : ℤ)) o i .neg
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Returning from an inner loop advances the next outer loop by one cell. -/
private lemma catalogPoly_advance {c C : ℕ} (x : List Bool) (q : ℕ)
    (h : Fin (c + 1) → ℤ) (o : List Bool) (i : Fin (c + 1)) :
    (catalogPolyUnaryTM c C).tm.step
      (catalogPolyCfg x q (.advance ⟨i.val, by omega⟩) h o) =
      catalogPolyCfg x q (.loop i) (Function.update h i (h i + 1)) o := by
  simp only [MultiTapeTM.step, catalogPolyUnaryTM, catalogPolyCfg, i.isLt, ↓reduceDIte]
  simpa [catalogPolyCfg] using catalogPolyMove_apply x q
    (.advance ⟨i.val, by omega⟩) (.loop i) h o i .pos

/-- Exact time for a full nest of unary loops, with `r` loop levels. -/
private def catalogPolyCost (q C : ℕ) : ℕ → ℕ
  | 0 => C + 1
  | r + 1 => q * (catalogPolyCost q C r + 2) + q + 2

/-- A loop at level `i` executes its remaining iterations, resets its head,
and returns to its parent with exactly `C*q^i` new symbols per iteration.

**Proof sketch.** Induct on the nesting level, then on the number of remaining
iterations. At level zero the body is the finite emission chain. At higher
levels it is a complete inner loop. Each body has one dispatch and one parent
advance; after the final iteration the unary rewind restores the head to zero.
The invariant leaves all outer heads arbitrary, making recursive calls composable. -/
private lemma catalogPoly_loop {c C : ℕ} (x : List Bool) (q : ℕ) (_hq : 0 < q) :
    ∀ i (hi : i < c + 1) (h : Fin (c + 1) → ℤ)
      (_hh : ∀ k, k.val ≤ i → h k = 0) (o : List Bool) (r j : ℕ), j + r = q →
    (catalogPolyUnaryTM c C).tm.runFrom
      (catalogPolyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (j : ℤ)) o)
      (r * (catalogPolyCost q C i + 2) + q + 2) =
      catalogPolyCfg x q (.advance ⟨i + 1, by omega⟩) h
        (o ++ List.replicate (r * (C * q ^ i)) true) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi h hh o r
    have hbody (j : ℕ) (hj : j < q) (o : List Bool) :
        (catalogPolyUnaryTM c C).tm.runFrom
          (catalogPolyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (j : ℤ)) o)
          (catalogPolyCost q C i + 2) =
        catalogPolyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ ((j : ℤ) + 1))
          (o ++ List.replicate (C * q ^ i) true) := by
      let h' := Function.update h ⟨i, hi⟩ (j : ℤ)
      have hread : (catalogPolyCfg (C := C) x q (.loop ⟨i, hi⟩) h' o).workTapeSymbols ⟨i, hi⟩ =
          some true := by simp [h', catalogPolyCfg, Cfg.workTapeSymbols, catalogPolyTape, hj]
      have hs : (catalogPolyUnaryTM c C).tm.step (catalogPolyCfg x q (.loop ⟨i, hi⟩) h' o) =
          catalogPolyCfg x q (if hz : i = 0 then .emit ⟨C, by omega⟩
            else .loop ⟨i - 1, by omega⟩) h' o := by
        unfold MultiTapeTM.step
        change ((catalogPolyUnaryTM c C).tm.tr (.loop ⟨i, hi⟩) _ _).apply _ = _
        simp only [catalogPolyUnaryTM, hread, reduceCtorEq, ↓reduceIte]
        apply Cfg.ext <;> simp [catalogPolyCfg, Action.apply]
      by_cases hz : i = 0
      · subst i
        simp only [↓reduceDIte] at hs
        change (catalogPolyUnaryTM c C).tm.runFrom (catalogPolyCfg x q (.loop 0) h' o) _ = _
        rw [show catalogPolyCost q C 0 + 2 = 1 + (C + 1) + 1 by simp [catalogPolyCost]; omega,
          MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add,
          show (catalogPolyUnaryTM c C).tm.runFrom (catalogPolyCfg x q (.loop 0) h' o) 1 =
            catalogPolyCfg x q (.emit ⟨C, by omega⟩) h' o by simpa using hs,
          catalogPoly_emit x q h' C (le_refl C),
          MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
        simpa [h'] using catalogPoly_advance (C := C) x q h'
          (o ++ List.replicate C true) (⟨0, hi⟩ : Fin (c + 1))
      · have hlow : ∀ k : Fin (c + 1), k.val ≤ i - 1 → h' k = 0 := by
          intro k hk
          have hne : k ≠ ⟨i, hi⟩ := by intro he; have := congrArg Fin.val he; simp at this; omega
          simp only [h', Function.update_of_ne hne]
          exact hh k (by omega)
        have hinner := ih (i - 1) (by omega) (by omega) h' hlow o q 0 (by omega)
        have hupdate : Function.update h' ⟨i - 1, by omega⟩ 0 = h' := by
          rw [← hlow ⟨i - 1, by omega⟩ (le_refl _)]
          exact Function.update_eq_self _ _
        have hi' : i - 1 + 1 = i := by omega
        have hout : q * (C * q ^ (i - 1)) = C * q ^ i := by
          calc
            q * (C * q ^ (i - 1)) = C * (q ^ (i - 1) * q) := by ring
            _ = C * q ^ i := by simp only [← Nat.pow_succ, Nat.succ_eq_add_one, hi']
        simp only [dif_neg hz] at hs
        simp only [Nat.cast_zero] at hinner
        rw [hupdate] at hinner
        have hinner' : (catalogPolyUnaryTM c C).tm.runFrom
            (catalogPolyCfg x q (.loop ⟨i - 1, by omega⟩) h' o) (catalogPolyCost q C i) =
            catalogPolyCfg x q (.advance ⟨i, by omega⟩) h'
              (o ++ List.replicate (C * q ^ i) true) := by
          have hcost : q * (catalogPolyCost q C (i - 1) + 2) + q + 2 =
              catalogPolyCost q C i := by
            calc
              _ = catalogPolyCost q C (i - 1 + 1) := rfl
              _ = catalogPolyCost q C i := by rw [hi']
          simpa only [hcost, hi', hout] using hinner
        change (catalogPolyUnaryTM c C).tm.runFrom (catalogPolyCfg x q (.loop ⟨i, hi⟩) h' o) _ = _
        rw [show catalogPolyCost q C i + 2 = 1 + catalogPolyCost q C i + 1 by omega,
          MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add,
          show (catalogPolyUnaryTM c C).tm.runFrom (catalogPolyCfg x q (.loop ⟨i, hi⟩) h' o) 1 =
            catalogPolyCfg x q (.loop ⟨i - 1, by omega⟩) h' o by simpa using hs,
          hinner', MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
        simpa [h'] using catalogPoly_advance (C := C) x q h'
          (o ++ List.replicate (C * q ^ i) true) (⟨i, hi⟩ : Fin (c + 1))
    induction r generalizing o with
    | zero =>
      intro j hj
      have hj' : j = q := by omega
      subst j
      have hs : (catalogPolyUnaryTM c C).tm.step
          (catalogPolyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (q : ℤ)) o) =
          catalogPolyCfg x q (.rewind ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ ((q : ℤ) - 1)) o := by
        unfold MultiTapeTM.step
        change ((catalogPolyUnaryTM c C).tm.tr (.loop ⟨i, hi⟩) _ _).apply _ = _
        simp only [catalogPolyUnaryTM, Cfg.workTapeSymbols, catalogPolyCfg, Function.update_self,
          catalogPolyTape, lt_self_iff_false, and_false, ↓reduceIte]
        simpa [catalogPolyCfg, sub_eq_add_neg] using catalogPolyMove_apply x q (.loop ⟨i, hi⟩)
          (.rewind ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (q : ℤ)) o ⟨i, hi⟩ .neg
      simp only [Nat.zero_mul, Nat.zero_add, List.replicate_zero, List.append_nil]
      rw [MultiTapeTM.runFrom_succ_eq_step, hs, catalogPoly_rewind x q h o ⟨i, hi⟩ q (le_refl q)]
      rw [← hh ⟨i, hi⟩ (le_refl _), Function.update_eq_self]
    | succ r ihr =>
      intro j hj
      have hjq : j < q := by omega
      rw [show (r + 1) * (catalogPolyCost q C i + 2) + q + 2 =
          (catalogPolyCost q C i + 2) + (r * (catalogPolyCost q C i + 2) + q + 2) by ring,
        MultiTapeTM.runFrom_add, hbody j hjq]
      have hr := ihr (o ++ List.replicate (C * q ^ i) true) (j + 1) (by omega)
      simp only [Nat.cast_add, Nat.cast_one] at hr
      rw [hr, List.append_assoc, ← List.replicate_add]
      congr 3
      ring

/-- Writing at the first blank extends a unary tape by exactly one cell. -/
private lemma catalogPolyTape_write (q : ℕ) :
    Function.update (catalogPolyTape q) (q : ℤ) (some true) = catalogPolyTape (q + 1) := by
  funext z
  by_cases hz : z = (q : ℤ)
  · subst z
    simp [catalogPolyTape]
  · rw [Function.update_of_ne hz]
    unfold catalogPolyTape
    have he : (0 ≤ z ∧ z < (q : ℤ)) ↔ (0 ≤ z ∧ z < ((q + 1 : ℕ) : ℤ)) := by omega
    simp only [he]

/-- The full loop costs at most a constant times the number of box points.
Each level's rewinds are charged to its `q` completed body iterations. -/
private lemma catalogPolyCost_le (q C : ℕ) (hq : 0 < q) : ∀ r,
    catalogPolyCost q C r ≤ (C + 1 + 5 * r) * q ^ r := by
  intro r
  induction r with
  | zero => simp [catalogPolyCost]
  | succ r ih =>
    have hqpow : q ≤ q ^ (r + 1) := by
      simpa only [Nat.pow_one] using Nat.pow_le_pow_right hq (show 1 ≤ r + 1 by omega)
    have hpos : 1 ≤ q ^ (r + 1) := Nat.one_le_pow _ _ hq
    calc
      catalogPolyCost q C (r + 1) = q * (catalogPolyCost q C r + 2) + q + 2 := rfl
      _ ≤ q * ((C + 1 + 5 * r) * q ^ r + 2) + q + 2 :=
        Nat.add_le_add_right (Nat.add_le_add_right
          (Nat.mul_le_mul_left q (Nat.add_le_add_right ih 2)) q) 2
      _ = (C + 1 + 5 * r) * q ^ (r + 1) + 3 * q + 2 := by rw [Nat.pow_succ]; ring
      _ ≤ (C + 1 + 5 * r) * q ^ (r + 1) + 5 * q ^ (r + 1) := by omega
      _ = (C + 1 + 5 * (r + 1)) * q ^ (r + 1) := by ring

/-- Configurations while copying the input length to every unary loop tape. -/
private def catalogPolyCopyCfg (c C : ℕ) (x : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    Cfg (c + 1) Bool (CatalogPolyControl c C) x :=
  ⟨some .copy, ⟨i + 1, by omega⟩, fun _ => catalogPolyTape i, fun _ => i, []⟩

/-- One input scan copies its length, in unary, onto every loop tape at once. -/
private lemma catalogPoly_copy (c C : ℕ) (x : List Bool) : ∀ i (hi : i ≤ x.length),
    (catalogPolyUnaryTM c C).tm.runFrom ((catalogPolyUnaryTM c C).tm.initCfg x) i =
      catalogPolyCopyCfg c C x i hi := by
  intro i
  induction i with
  | zero =>
    intro hi
    apply Cfg.ext
    · rfl
    · rfl
    · funext k z
      simp [MultiTapeTM.initCfg, Cfg.init, catalogPolyCopyCfg, catalogPolyTape,
        show ¬(0 ≤ z ∧ z < (0 : ℤ)) by omega]
    · rfl
    · rfl
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hin : (catalogPolyCopyCfg c C x i (by omega)).inputSymbol = some x[i] :=
      inputSymbolInner i (by simp [catalogPolyCopyCfg, Nat.add_comm]) (by omega)
    unfold MultiTapeTM.step
    change ((catalogPolyUnaryTM c C).tm.tr .copy _ _).apply _ = _
    rw [hin]
    apply Cfg.ext
    · rfl
    · apply Fin.ext
      change (moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos).val = i + 1 + 1
      rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
    · funext k
      exact catalogPolyTape_write i
    · funext k
      simp [catalogPolyUnaryTM, catalogPolyCopyCfg, Action.apply, Nat.add_comm]
    · rfl

/-- The startup rewind moves all synchronized heads left, then enters the outermost loop. -/
private lemma catalogPoly_setup (c C : ℕ) (x : List Bool) (q : ℕ) : ∀ j (_hj : j ≤ q),
    (catalogPolyUnaryTM c C).tm.runFrom
      (catalogPolyCfg x q .setup (fun _ => (j : ℤ) - 1) []) (j + 1) =
      catalogPolyCfg x q (.loop (Fin.last c)) (fun _ => 0) [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;>
      simp [MultiTapeTM.step, catalogPolyUnaryTM, catalogPolyCfg, Cfg.workTapeSymbols, catalogPolyTape, Action.apply]
  | succ j ih =>
    intro hj
    have hs : (catalogPolyUnaryTM c C).tm.step
        (catalogPolyCfg x q .setup (fun _ => ((j + 1 : ℕ) : ℤ) - 1) []) =
        catalogPolyCfg x q .setup (fun _ => (j : ℤ) - 1) [] := by
      apply Cfg.ext <;>
        simp [MultiTapeTM.step, catalogPolyUnaryTM, catalogPolyCfg, Cfg.workTapeSymbols, catalogPolyTape,
          show (j : ℤ) < q by omega, Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Startup installs side length `|x|+1` and puts every loop head at zero.
The final extra unary cell handles empty input without a special case. -/
private lemma catalogPoly_start (c C : ℕ) (x : List Bool) :
    (catalogPolyUnaryTM c C).tm.runFrom ((catalogPolyUnaryTM c C).tm.initCfg x)
      (2 * (x.length + 1)) =
      catalogPolyCfg x (x.length + 1) (.loop (Fin.last c)) (fun _ => 0) [] := by
  have hs : (catalogPolyUnaryTM c C).tm.step
      (catalogPolyCopyCfg c C x x.length (le_refl _)) =
      catalogPolyCfg x (x.length + 1) .setup (fun _ => (x.length : ℤ) - 1) [] := by
    have hin : (catalogPolyCopyCfg c C x x.length (le_refl _)).inputSymbol = none := by
      simp [catalogPolyCopyCfg, Cfg.inputSymbol]
    unfold MultiTapeTM.step
    change ((catalogPolyUnaryTM c C).tm.tr .copy _ _).apply _ = _
    rw [hin]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero _
    · funext k
      exact catalogPolyTape_write x.length
    · funext k
      simp [catalogPolyUnaryTM, catalogPolyCopyCfg, catalogPolyCfg, Action.apply, sub_eq_add_neg]
    · rfl
  have hpre : (catalogPolyUnaryTM c C).tm.runFrom ((catalogPolyUnaryTM c C).tm.initCfg x)
      (x.length + 1) =
      catalogPolyCfg x (x.length + 1) .setup (fun _ => (x.length : ℤ) - 1) [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step', catalogPoly_copy c C x x.length (le_refl _), hs]
  rw [show 2 * (x.length + 1) = (x.length + 1) + (x.length + 1) by omega,
    MultiTapeTM.runFrom_add, hpre]
  exact catalogPoly_setup c C x (x.length + 1) x.length (by omega)

/-- The explicit generator computes the exact unary catalogPolynomial in linear time
in its number of box points. This includes coefficient zero and empty input.

**Proof sketch.** Startup costs `2(n+1)`. The full outer loop emits
`C(n+1)^(c+1)` symbols and costs at most `(C+1+5(c+1))(n+1)^(c+1)`.
One final transition halts; `n+1 ≤ (n+1)^(c+1)` absorbs startup. -/
private lemma catalogPoly_unary_computes (c C : ℕ) :
    (catalogPolyUnaryTM c C).ComputesFunInTime
      (fun x => List.replicate (C * (x.length + 1) ^ (c + 1)) true)
      (fun n => (C + 5 * (c + 1) + 4) * (n + 1) ^ (c + 1)) := by
  intro x
  have hl := catalogPoly_loop (c := c) (C := C) x (x.length + 1) (Nat.succ_pos _) c (by omega)
    (fun _ => 0) (by simp) [] (x.length + 1) 0 (by omega)
  have hout : (x.length + 1) * (C * (x.length + 1) ^ c) =
      C * (x.length + 1) ^ (c + 1) := by rw [Nat.pow_succ]; ring
  have hloop : (catalogPolyUnaryTM c C).tm.runFrom
      (catalogPolyCfg x (x.length + 1) (.loop (Fin.last c)) (fun _ => 0) [])
      (catalogPolyCost (x.length + 1) C (c + 1)) =
      catalogPolyCfg x (x.length + 1) (.advance (Fin.last (c + 1))) (fun _ => 0)
        (List.replicate (C * (x.length + 1) ^ (c + 1)) true) := by
    simpa [catalogPolyCost, hout] using hl
  have hbase : (catalogPolyUnaryTM c C).ComputesInTime x
      (List.replicate (C * (x.length + 1) ^ (c + 1)) true)
      (2 * (x.length + 1) + catalogPolyCost (x.length + 1) C (c + 1) + 1) := by
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add, catalogPoly_start, hloop]
    simp [MultiTapeTM.step, catalogPolyUnaryTM, catalogPolyCfg, Action.apply]
  apply hbase.mono
  have hp : x.length + 1 ≤ (x.length + 1) ^ (c + 1) := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos x.length)
      (show 1 ≤ c + 1 by omega)
  have hpos : 1 ≤ (x.length + 1) ^ (c + 1) := Nat.one_le_pow _ _ (Nat.succ_pos _)
  calc
    _ ≤ 2 * (x.length + 1) +
        (C + 1 + 5 * (c + 1)) * (x.length + 1) ^ (c + 1) + 1 :=
      Nat.add_le_add_right (Nat.add_le_add_left
        (catalogPolyCost_le (x.length + 1) C (Nat.succ_pos _) (c + 1)) _) 1
    _ ≤ (C + 1 + 5 * (c + 1)) * (x.length + 1) ^ (c + 1) +
        3 * (x.length + 1) ^ (c + 1) := by omega
    _ = _ := by ring


/-- Administrative actions for the captured length checker move only the
input and final (countdown) head. No tape is written. -/
private def lenAction (M : FinTM Bool) (m d : SignType) (b : Option Bool)
    (q : Option (M.State ⊕ (Fin 4 ⊕ Option Bool))) :
    Action (M.k + 1) Bool (M.State ⊕ (Fin 4 ⊕ Option Bool)) :=
  ⟨m, fun i => (none, if i.val < M.k then 0 else d), b, q⟩

/-- Capture a total generator, rewind the physical input, validate its pair
syntax, then compare the suffix length with the captured word's length.
Only the final comparison or rejection transition emits a verdict. -/
private def pairCountTM (M : FinTM Bool) : FinTM Bool where
  k := M.k + 1
  State := M.State ⊕ (Fin 4 ⊕ Option Bool)
  tm := {
    q₀ := .inl M.tm.q₀
    tr := fun q inp work => match q with
      | .inl s => captureAction Sum.inl (.inr (.inl 0))
          (M.tm.tr s inp fun i => work i.castSucc)
      | .inr (.inl q) => match q.val with
        | 0 => lenAction M 0 .neg none (some (.inr (.inl 1)))
        | 1 => controlAction .neg (some (.inr (.inl 2)))
        | 2 => match inp with
          | some _ => controlAction .neg (some (.inr (.inl 2)))
          | none => controlAction .pos (some (.inr (.inr none)))
        | _ => match inp with
          | none => lenAction M 0 0 (some true) none
          | some _ => match work (Fin.last M.k) with
            | none => lenAction M 0 0 (some false) none
            | some _ => lenAction M .pos .neg none (some (.inr (.inl 3)))
      | .inr (.inr none) => match inp with
        | none => lenAction M 0 0 (some false) none
        | some b => lenAction M .pos 0 none (some (.inr (.inr (some b))))
      | .inr (.inr (some b)) => match inp with
        | none => lenAction M 0 0 (some false) none
        | some d => if b = d then lenAction M .pos 0 none (some (.inr (.inr none)))
          else if b then lenAction M 0 0 (some false) none
          else lenAction M .pos 0 none (some (.inr (.inl 3))) }

/-- **The threaded length check**. Capture the unary generator applied to the decoded first
component, then validate the input pair and count its second component down against the captured
unary word; emit the single verdict. -/
def pairLenCheckTM (C e : ℕ) : FinTM Bool :=
  pairCountTM (bufferedCompTM (pairExtractTM true false) (polyUnaryTM C e))

/-- Checker configurations retain the completed generator bank and its
captured output; `r` is the number of still available countdown cells. -/
private def lenCfg (M : FinTM Bool) {x : List Bool} (c : Cfg M.k Bool M.State x)
    (q : Option (pairCountTM M).State) (i : ℕ) (hi : i ≤ x.length) (r : ℕ) :
    Cfg (M.k + 1) Bool (pairCountTM M).State x :=
  { captureCfg (fun s : M.State => (Sum.inl s : (pairCountTM M).State))
      (.inr (.inl 0)) [] [] c with
    state := q
    inputPos := ⟨i + 1, by omega⟩
    workTapePos := fun j => if h : j.val < M.k then c.workTapePos ⟨j, h⟩
      else (r : ℤ) - 1 }

/-- The checker's input read is independent of the saved generator bank. -/
private lemma lenCfg_read (M : FinTM Bool) {x : List Bool} (c : Cfg M.k Bool M.State x)
    (q : Option (pairCountTM M).State) (i : ℕ) (hi : i ≤ x.length) (r : ℕ) :
    (lenCfg M c q i hi r).inputSymbol = x[i]? :=
  inputSymbol_at _ i hi rfl

/-- A stationary or forward administrative action preserves all work tapes;
its last-head movement subtracts one precisely when consuming a cell. -/
private lemma lenAction_apply (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (q q' : Option (pairCountTM M).State)
    (i j r s : ℕ) (hi : i ≤ x.length) (hj : j ≤ x.length)
    (m d : SignType) (b : Option Bool)
    (hm : moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) m = ⟨j + 1, by omega⟩)
    (hd : (r : ℤ) - 1 + d.cast = (s : ℤ) - 1) :
    (lenAction M m d b q').apply (lenCfg M c q i hi r) =
      {lenCfg M c q' j hj s with output := b.toList} := by
  refine Cfg.ext rfl hm ?_ ?_ rfl
  · rfl
  · funext k
    by_cases hk : k.val < M.k
    · simp [lenAction, lenCfg, Action.apply, hk]
    · simpa [lenAction, lenCfg, Action.apply, hk] using hd

/-- Suffix comparison consumes one captured cell per input bit and emits one
verdict at termination. Empty suffixes succeed even with an empty counter.
**Proof sketch.** Induct on the suffix. A zero counter rejects a nonempty
suffix immediately; otherwise one silent step decrements both lengths. -/
private lemma lenSuffix_run (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (rest : List Bool) :
    ∀ pre (hx : x = pre ++ rest) r, r ≤ c.output.length →
    ∃ t ≤ rest.length + 1,
      ((pairCountTM M).tm.runFrom
        (lenCfg M c (some (.inr (.inl 3))) pre.length (by simp [hx]) r) t).state = none ∧
      ((pairCountTM M).tm.runFrom
        (lenCfg M c (some (.inr (.inl 3))) pre.length (by simp [hx]) r) t).output =
          [decide (rest.length ≤ r)] := by
  induction rest with
  | nil =>
    intro pre hx r hr
    refine ⟨1, by simp, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (((pairCountTM M).tm.tr (.inr (.inl 3)) _ _).apply _).state = none ∧ _
    rw [lenCfg_read]
    simp [hx, pairCountTM, lenAction, lenCfg, captureCfg, Action.apply]
  | cons b rest ih =>
    intro pre hx r hr
    cases r with
    | zero =>
      refine ⟨1, by simp, ?_⟩
      simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
      unfold MultiTapeTM.step
      change (((pairCountTM M).tm.tr (.inr (.inl 3)) _ _).apply _).state = none ∧ _
      rw [lenCfg_read]
      simp [hx, pairCountTM, lenAction, lenCfg, captureCfg, Cfg.workTapeSymbols,
        bufferTape_left, Action.apply]
    | succ r =>
      have hs : (pairCountTM M).tm.step
          (lenCfg M c (some (.inr (.inl 3))) pre.length (by simp [hx]) (r + 1)) =
          lenCfg M c (some (.inr (.inl 3))) (pre.length + 1) (by simp [hx]) r := by
        unfold MultiTapeTM.step
        change ((pairCountTM M).tm.tr (.inr (.inl 3)) _ _).apply _ = _
        rw [lenCfg_read]
        have hin : x[pre.length]? = some b := by simp [hx]
        have hw : (lenCfg M c (some (.inr (.inl 3))) pre.length
            (by simp [hx]) (r + 1)).workTapeSymbols (Fin.last M.k) =
              some (c.output[r]'(by omega)) := by
          simp [lenCfg, captureCfg, Cfg.workTapeSymbols, bufferTape,
            List.getElem?_eq_getElem (by omega : r < c.output.length)]
        simp only [pairCountTM, hin, hw]
        exact lenAction_apply M c _ _ pre.length (pre.length + 1) (r + 1) r
          (by simp [hx]) (by simp [hx]) .pos .neg none
          (moveInputPos_pos_of_ne_right _ (by simp [hx])) (by simp [SignType.cast]; omega)
      obtain ⟨t, ht, hh, ho⟩ := ih (pre ++ [b]) (by simpa [List.append_assoc] using hx)
        r (by omega)
      refine ⟨1 + t, by simp only [List.length_cons]; omega, ?_⟩
      rw [MultiTapeTM.runFrom_add]
      simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
      rw [hs]
      simpa using And.intro hh ho

/-- The first half of an aligned block changes only finite control and the
input position; countdown cells remain untouched during validation. -/
private lemma lenParse_first (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (pre rest : List Bool) (b : Bool) (r : ℕ)
    (hx : x = pre ++ b :: rest) :
    (pairCountTM M).tm.step
      (lenCfg M c (some (.inr (.inr none))) pre.length (by simp [hx]) r) =
      lenCfg M c (some (.inr (.inr (some b)))) (pre.length + 1) (by simp [hx]) r := by
  unfold MultiTapeTM.step
  change ((pairCountTM M).tm.tr (.inr (.inr none)) _ _).apply _ = _
  rw [lenCfg_read]
  have hin : x[pre.length]? = some b := by simp [hx]
  simp only [pairCountTM, hin]
  exact lenAction_apply M c _ _ pre.length (pre.length + 1) r r
    (by simp [hx]) (by simp [hx]) .pos 0 none
    (moveInputPos_pos_of_ne_right _ (by simp [hx])) (by simp [SignType.cast])

/-- Two parser steps either advance over a doubled bit, enter the suffix
comparison at `01`, or reject `10`. Nothing is emitted on a valid block. -/
private lemma lenParse_block (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (pre rest : List Bool) (b d : Bool) (r : ℕ)
    (hx : x = pre ++ b :: d :: rest) :
    (pairCountTM M).tm.runFrom
      (lenCfg M c (some (.inr (.inr none))) pre.length (by simp [hx]) r) 2 =
      if b = d then lenCfg M c (some (.inr (.inr none)))
          (pre.length + 2) (by simp [hx]) r
      else if b then {lenCfg M c none (pre.length + 1) (by simp [hx]) r with output := [false]}
      else lenCfg M c (some (.inr (.inl 3))) (pre.length + 2) (by simp [hx]) r := by
  change (pairCountTM M).tm.step ((pairCountTM M).tm.step _) = _
  rw [lenParse_first M c pre (d :: rest) b r hx]
  unfold MultiTapeTM.step
  change ((pairCountTM M).tm.tr (.inr (.inr (some b))) _ _).apply _ = _
  rw [lenCfg_read]
  have hin : x[pre.length + 1]? = some d := by simp [hx]
  rw [hin]
  have hm : moveInputPos (⟨pre.length + 1 + 1, by simp [hx]⟩ : Fin (x.length + 2)) .pos =
      ⟨pre.length + 2 + 1, by simp [hx]; omega⟩ :=
    moveInputPos_pos_of_ne_right _ (by simp [hx])
  cases b <;> cases d <;>
    simp only [pairCountTM, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
  all_goals first
    | exact lenAction_apply M c _ _ (pre.length + 1) (pre.length + 2) r r
        (by simp [hx]) (by simp [hx]) .pos 0 none hm (by simp [SignType.cast])
    | exact lenAction_apply M c _ _ (pre.length + 1) (pre.length + 1) r r
        (by simp [hx]) (by simp [hx]) 0 0 (some false)
        (moveInputPos_zero _) (by simp [SignType.cast])

/-- Aligned validation followed by countdown comparison decides the payload
bound in at most one more than the unread input length.
**Proof sketch.** Induct over two-bit blocks, using the existing parser's
same grammar and induction pattern. Equal-bit blocks preserve the counter;
`01` invokes suffix comparison; malformed endings and `10` reject. -/
private lemma lenParse_run (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (rest : List Bool) :
    ∀ pre (hx : x = pre ++ rest) r, r ≤ c.output.length →
    ∃ t ≤ rest.length + 1,
      ((pairCountTM M).tm.runFrom
        (lenCfg M c (some (.inr (.inr none))) pre.length (by simp [hx]) r) t).state = none ∧
      ((pairCountTM M).tm.runFrom
        (lenCfg M c (some (.inr (.inr none))) pre.length (by simp [hx]) r) t).output =
          [match pairDecode rest with
            | some (_, b) => decide (b.length ≤ r)
            | none => false] := by
  induction rest using List.twoStepInduction with
  | nil =>
    intro pre hx r hr
    refine ⟨1, by simp, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (((pairCountTM M).tm.tr (.inr (.inr none)) _ _).apply _).state = none ∧ _
    rw [lenCfg_read]
    simp [hx, pairCountTM, lenAction, lenCfg, captureCfg, Action.apply, pairDecode]
  | singleton b =>
    intro pre hx r hr
    refine ⟨2, by simp, ?_⟩
    change ((pairCountTM M).tm.step ((pairCountTM M).tm.step _)).state = none ∧
      ((pairCountTM M).tm.step ((pairCountTM M).tm.step _)).output = _
    rw [lenParse_first M c pre [] b r hx]
    unfold MultiTapeTM.step
    change (((pairCountTM M).tm.tr (.inr (.inr (some b))) _ _).apply _).state = none ∧ _
    rw [lenCfg_read]
    cases b <;> simp [hx, pairCountTM, lenAction, lenCfg, captureCfg, Action.apply, pairDecode]
  | cons_cons b d rest ih _ =>
    intro pre hx r hr
    by_cases h : b = d
    · subst d
      obtain ⟨t, ht, hs, ho⟩ := ih (pre ++ [b, b])
        (by simpa [List.append_assoc] using hx) r hr
      refine ⟨2 + t, by simp only [List.length_cons] at *; omega, ?_⟩
      rw [MultiTapeTM.runFrom_add, lenParse_block M c pre rest b b r hx, if_pos rfl]
      simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
      refine ⟨hs, ?_⟩
      cases b <;> cases hd : pairDecode rest with
        | none => simpa [pairDecode, hd] using ho
        | some p => cases p; simpa [pairDecode, hd] using ho
    · cases b <;> cases d
      · exact False.elim (h rfl)
      · obtain ⟨t, ht, hs, ho⟩ := lenSuffix_run M c rest (pre ++ [false, true])
          (by simpa [List.append_assoc] using hx) r hr
        refine ⟨2 + t, by simp only [List.length_cons]; omega, ?_⟩
        rw [MultiTapeTM.runFrom_add, lenParse_block M c pre rest false true r hx]
        simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
        exact ⟨hs, by simpa [pairDecode] using ho⟩
      · refine ⟨2, by simp, ?_⟩
        rw [lenParse_block M c pre rest true false r hx]
        simp [lenCfg, pairDecode]
      · exact False.elim (h rfl)

/-- Quantitative input rewind, adapted from the wrapper controller's proved
`timed_rewind` pattern using the public `rewind_scan` interface.
**Proof sketch.** One mandatory left move is followed by exactly the new
position plus one scan steps. Work tapes and output are preserved. -/
private lemma catalogRewind {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (start scan : S) (dest : Option S)
    (hstart : ∀ inp work, tm.tr start inp work = controlAction .neg (some scan))
    (hscan : ∀ inp work, tm.tr scan inp work = match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest)
    (c : Cfg k Bool S x) (hs : c.state = some start) :
    ∃ r ≤ c.inputPos.val + 2,
      tm.runFrom c r = {c with state := dest, inputPos := 1} := by
  have hstep : tm.step c =
      {c with state := some scan, inputPos := moveInputPos c.inputPos .neg} := by
    unfold MultiTapeTM.step
    rw [hs]
    dsimp only
    rw [hstart, controlAction_apply]
  have hp : (moveInputPos c.inputPos .neg).val ≤ x.length := by
    rw [moveInputPos_neg_val]
    have := c.inputPos.isLt
    omega
  refine ⟨1 + ((moveInputPos c.inputPos .neg).val + 1), ?_, ?_⟩
  · rw [moveInputPos_neg_val]; omega
  · rw [MultiTapeTM.runFrom_add]
    change tm.runFrom (tm.step c) _ = _
    rw [hstep, rewind_scan tm scan dest hscan _ rfl hp]

/-- A completed generator is captured without physical output, then its
last cell and the first physical input cell are exposed for comparison.
**Proof sketch.** Use the least source halting time to discharge `capture_run`'s
liveness guard. One step moves the capture head left; quantitative rewind
restores the input head while preserving the completed generator bank. -/
private lemma lenStart (M : FinTM Bool) (x w : List Bool) (T : ℕ)
    (hM : M.ComputesInTime x w T) :
    ∃ t ≤ T + x.length + 4, ∃ c : Cfg M.k Bool M.State x,
      c.output = w ∧
      (pairCountTM M).tm.runFrom ((pairCountTM M).tm.initCfg x) t =
        lenCfg M c (some (.inr (.inr none))) 0 (by omega) c.output.length := by
  classical
  have hh : ∃ t, (M.tm.runFrom (M.tm.initCfg x) t).state = none :=
    ⟨T, ((computesInTime_iff _ _ _ _).mp hM).1⟩
  let t := Nat.find hh
  let c := M.tm.runFrom (M.tm.initCfg x) t
  have ht : t ≤ T := Nat.find_min' hh ((computesInTime_iff _ _ _ _).mp hM).1
  have hs : c.state = none := Nat.find_spec hh
  have hc : M.ComputesInTime x c.output t := (computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
  have ho : c.output = w := hc.output_unique hM
  let emb : M.State → (pairCountTM M).State := Sum.inl
  let ret : (pairCountTM M).State := .inr (.inl 0)
  have hinit : (pairCountTM M).tm.initCfg x = captureCfg emb ret [] [] (M.tm.initCfg x) := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i; simp [captureCfg, MultiTapeTM.initCfg, Cfg.init]
    · funext i; simp [captureCfg, MultiTapeTM.initCfg, Cfg.init]
  have hcap : (pairCountTM M).tm.runFrom ((pairCountTM M).tm.initCfg x) t =
      captureCfg emb ret [] [] c := by
    rw [hinit]
    exact capture_run M.tm (pairCountTM M).tm emb ret (fun _ _ _ => rfl)
      [] [] _ t (fun s hst => Nat.find_min hh hst)
  let ready : Cfg (M.k + 1) Bool (pairCountTM M).State x :=
    {lenCfg M c (some (.inr (.inl 1))) 0 (by omega) c.output.length with
      inputPos := c.inputPos}
  have hback : (pairCountTM M).tm.step (captureCfg emb ret [] [] c) = ready := by
    have hstate : (captureCfg emb ret [] [] c).state = some ret := by simp [captureCfg, hs]
    simp only [MultiTapeTM.step, hstate]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero _
    · rfl
    · funext i
      by_cases hi : i.val < M.k <;>
        simp [pairCountTM, ret, lenAction, Action.apply, captureCfg, ready, lenCfg, hi,
          sub_eq_add_neg]
    · rfl
  obtain ⟨r, hrle, hr⟩ := catalogRewind (pairCountTM M).tm
    (.inr (.inl 1)) (.inr (.inl 2)) (some (.inr (.inr none)))
    (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl) ready rfl
  refine ⟨t + 1 + r, ?_, c, ho, ?_⟩
  · change r ≤ c.inputPos.val + 2 at hrle
    have := c.inputPos.isLt
    omega
  · rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, hcap]
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    rw [hback, hr]
    rfl

/-- The captured checker compares a valid pair's payload with the length of
the generator's output, and rejects every malformed input.
**Proof sketch.** Compose the silent capture/rewind prefix with the aligned
parser and countdown ledger, then absorb the two linear scans. -/
private lemma pairCount_computes {M : FinTM Bool} {g : List Bool → List Bool}
    {T : ℕ → ℕ} (hM : M.ComputesFunInTime g T) :
    (pairCountTM M).ComputesFunInTime
      (fun x => [match pairDecode x with
        | some (_, b) => decide (b.length ≤ (g x).length)
        | none => false]) (fun n => T n + 2 * n + 5) := by
  intro x
  obtain ⟨t, ht, c, ho, hstart⟩ := lenStart M x (g x) (T x.length) (hM x)
  obtain ⟨r, hr, hs, hout⟩ := lenParse_run M c x [] rfl c.output.length (le_refl _)
  have hc : (pairCountTM M).ComputesInTime x
      [match pairDecode x with
        | some (_, b) => decide (b.length ≤ (g x).length)
        | none => false] (t + r) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart]
    exact ⟨hs, by simpa only [ho] using hout⟩
  exact hc.mono (by dsimp only; omega)

/-- Copy the physical input, erase its final false-run and last true, rewind,
then replay. An all-false input halts silently during the reverse scan. -/
private def rawStripTM : FinTM Bool where
  k := 1
  State := Fin 4
  tm := {
    q₀ := 0
    tr := fun q inp work => match q.val with
      | 0 => match inp with
        | some b => ⟨.pos, fun _ => (some (some b), .pos), none, some 0⟩
        | none => ⟨0, fun _ => (none, .neg), none, some 1⟩
      | 1 => match work 0 with
        | none => ⟨0, fun _ => (none, 0), none, none⟩
        | some b => ⟨0, fun _ => (some none, .neg), none, some (if b then 2 else 1)⟩
      | 2 => match work 0 with
        | some _ => ⟨0, fun _ => (none, .neg), none, some 2⟩
        | none => ⟨0, fun _ => (none, .pos), none, some 3⟩
      | _ => match work 0 with
        | some b => ⟨0, fun _ => (none, .pos), some b, some 3⟩
        | none => ⟨0, fun _ => (none, 0), none, none⟩ }

/-- Raw-strip configurations expose the indexed input and a contiguous buffer. -/
private def stripCfg (x : List Bool) (q : Option (Fin 4)) (i : ℕ) (hi : i ≤ x.length)
    (w : List Bool) (h : ℤ) (out : List Bool) : Cfg 1 Bool (Fin 4) x :=
  ⟨q, ⟨i + 1, by omega⟩, fun _ => bufferTape w, fun _ => h, out⟩

/-- Erasing the last written cell restores exactly the shorter buffer. -/
private lemma catalogBuffer_erase (w : List Bool) (b : Bool) :
    Function.update (bufferTape (w ++ [b])) (w.length : ℤ) none = bufferTape w := by
  rw [bufferTape_append, Function.update_idem]
  funext z
  by_cases hz : z = (w.length : ℤ)
  · subst z; simp
  · simp [Function.update_of_ne hz]

/-- The forward copy is silent and installs exactly the scanned input prefix.
**Proof sketch.** One input step appends the next bit at the buffer's right
blank; the input and work heads both advance once. -/
private lemma rawStrip_copy (x : List Bool) : ∀ j (hj : j ≤ x.length),
    rawStripTM.tm.runFrom (rawStripTM.tm.initCfg x) j =
      stripCfg x (some 0) j hj (x.take j) j [] := by
  intro j
  induction j with
  | zero => intro hj; apply Cfg.ext <;> simp [rawStripTM, stripCfg]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hin : (stripCfg x (some 0) j (by omega) (x.take j) j []).inputSymbol =
        some (x[j]'(by omega)) := inputSymbolInner j (by simp [stripCfg]; omega) (by omega)
    unfold MultiTapeTM.step
    change (rawStripTM.tm.tr (0 : Fin 4) _ _).apply _ = _
    rw [hin]
    refine Cfg.ext rfl (moveInputPos_pos_of_ne_right _ (by simp [stripCfg]; omega)) ?_ ?_ rfl
    · funext k
      change Function.update (bufferTape (x.take j)) (j : ℤ) (some (x[j]'(by omega))) =
        bufferTape (x.take (j + 1))
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      simpa only [List.length_take, Nat.min_eq_left (by omega : j ≤ x.length)] using
        (bufferTape_append (x.take j) (x[j]'(by omega))).symm
    · funext k; simp [rawStripTM, stripCfg, Action.apply]

/-- Rewinding the validated buffer from cell `j-1` takes `j+1` transitions.
**Proof sketch.** At the left blank, move right and enter replay. Otherwise
read a buffer cell, move left, and invoke the induction hypothesis. -/
private lemma rawStrip_rewind (x a : List Bool)
    (i : ℕ) (hi : i ≤ x.length) : ∀ j, j ≤ a.length →
    rawStripTM.tm.runFrom
      (stripCfg x (some 2) i hi a ((j : ℤ) - 1) []) (j + 1) =
      stripCfg x (some 3) i hi a 0 [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    simp only [rawStripTM, stripCfg, Cfg.workTapeSymbols, Nat.cast_zero,
      zero_sub, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext k; simp [Action.apply]
  | succ j ih =>
    intro hj
    have hs : rawStripTM.tm.step
        (stripCfg x (some 2) i hi a (((j + 1 : ℕ) : ℤ) - 1) []) =
        stripCfg x (some 2) i hi a ((j : ℤ) - 1) [] := by
      have hz : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [hz]
      unfold MultiTapeTM.step
      simp only [rawStripTM, stripCfg, Cfg.workTapeSymbols, bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < a.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext k; simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Replay appends exactly the visited buffer prefix and preserves its tape.
**Proof sketch.** The same replay invariant as the shared extractor: induct
on the number of visited cells and use the next-prefix equation for lists. -/
private lemma rawStrip_replay (x a : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    ∀ j (_hj : j ≤ a.length),
    rawStripTM.tm.runFrom (stripCfg x (some 3) i hi a 0 []) j =
      stripCfg x (some 3) i hi a j (a.take j) := by
  intro j
  induction j with
  | zero => intro hj; rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    unfold MultiTapeTM.step
    simp only [rawStripTM, stripCfg, Cfg.workTapeSymbols, bufferTape_nat,
      List.getElem?_eq_getElem (by omega : j < a.length)]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
    · funext k; simp [Action.apply]
    · change a.take j ++ [a[j]'(by omega)] = a.take (j + 1)
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      rfl

/-- Rewind followed by replay halts with exactly the retained buffer.
**Proof sketch.** The rewind costs `|a|+1`; replay and its final blank test
cost another `|a|+1`, and no earlier phase has emitted anything. -/
private lemma rawStrip_finish (x a : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    (rawStripTM.tm.runFrom (stripCfg x (some 2) i hi a (a.length - 1) [])
      (2 * (a.length + 1))).state = none ∧
    (rawStripTM.tm.runFrom (stripCfg x (some 2) i hi a (a.length - 1) [])
      (2 * (a.length + 1))).output = a := by
  have htime : 2 * (a.length + 1) = (a.length + 1) + (a.length + 1) := by omega
  rw [htime, MultiTapeTM.runFrom_add, rawStrip_rewind x a i hi a.length (le_refl _),
    MultiTapeTM.runFrom_succ_eq_step', rawStrip_replay x a i hi a.length (le_refl _)]
  simp [MultiTapeTM.step, rawStripTM, stripCfg, Cfg.workTapeSymbols, Action.apply]

/-- The reverse phase erases the last cell and moves left, branching to
replay preparation precisely when the erased bit is true. -/
private lemma rawStrip_erase (x w : List Bool) (i : ℕ) (hi : i ≤ x.length) (b : Bool) :
    rawStripTM.tm.step
      (stripCfg x (some 1) i hi (w ++ [b]) ((w ++ [b]).length - 1) []) =
      stripCfg x (some (if b then 2 else 1)) i hi w (w.length - 1) [] := by
  have hz : (((w ++ [b]).length : ℕ) : ℤ) - 1 = w.length := by simp
  rw [hz]
  unfold MultiTapeTM.step
  simp only [stripCfg, rawStripTM, Cfg.workTapeSymbols, bufferTape_nat,
    List.getElem?_append_right (by omega : w.length ≤ w.length), Nat.sub_self,
    List.getElem?_cons_zero]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext k; exact catalogBuffer_erase w b
  · funext k; simp [Action.apply, sub_eq_add_neg]

/-- Reverse erasure implements `splitAtLastTrue` exactly, including rejection
of every all-false word.
**Proof sketch.** Induct from the right. A final false is erased and the
induction continues. A final true is erased and the retained prefix is
rewound and replayed. These are exactly the `reverse.dropWhile` equations. -/
private lemma rawStrip_trim (x w : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    ∃ t ≤ 3 * (w.length + 1),
      (rawStripTM.tm.runFrom (stripCfg x (some 1) i hi w (w.length - 1) []) t).state = none ∧
      (rawStripTM.tm.runFrom (stripCfg x (some 1) i hi w (w.length - 1) []) t).output =
        (splitAtLastTrue w).getD [] := by
  induction w using List.reverseRecOn with
  | nil =>
    refine ⟨1, by simp, ?_⟩
    simp [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.step, rawStripTM, stripCfg,
      Cfg.workTapeSymbols, Action.apply, splitAtLastTrue]
  | append_singleton w b ih =>
    cases b with
    | false =>
      obtain ⟨t, ht, hs, ho⟩ := ih
      refine ⟨t + 1, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step, rawStrip_erase]
      exact ⟨hs, by simpa [splitAtLastTrue] using ho⟩
    | true =>
      refine ⟨2 * (w.length + 1) + 1,
        by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step, rawStrip_erase]
      simpa [splitAtLastTrue] using rawStrip_finish x w i hi

/-- Raw marker stripping runs in linear time, with physical output delayed
until the last true has been located and removed.
**Proof sketch.** Copy in `|x|+1` steps, including the right-blank turn;
the reverse/replay ledger uses at most another `3(|x|+1)` steps. -/
private lemma rawStrip_computes : rawStripTM.ComputesFunInTime
    (fun x => (splitAtLastTrue x).getD []) (fun n => 4 * (n + 1)) := by
  intro x
  have hstart : rawStripTM.tm.runFrom (rawStripTM.tm.initCfg x) (x.length + 1) =
      stripCfg x (some 1) x.length (le_refl _) x (x.length - 1) [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step', rawStrip_copy x x.length (le_refl _)]
    have hin : (stripCfg x (some 0) x.length (le_refl _) (x.take x.length) x.length []).inputSymbol =
        none := by simp [stripCfg, Cfg.inputSymbol]
    unfold MultiTapeTM.step
    change (rawStripTM.tm.tr (0 : Fin 4) _ _).apply _ = _
    rw [hin]
    apply Cfg.ext <;> simp [rawStripTM, stripCfg, Action.apply, sub_eq_add_neg]
  obtain ⟨t, ht, hs, ho⟩ := rawStrip_trim x x x.length (le_refl _)
  have hc : rawStripTM.ComputesInTime x ((splitAtLastTrue x).getD []) (x.length + 1 + t) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart]
    exact ⟨hs, ho⟩
  exact hc.mono (by dsimp only; omega)

/-- A finite scanner emits whether its input contains a true bit. -/
private def anyTrueTM : FinTM Bool where
  k := 0
  State := Unit
  tm := {
    q₀ := ()
    tr := fun _ inp _ => match inp with
      | some false => ⟨.pos, fun i => i.elim0, none, some ()⟩
      | some true => ⟨0, fun i => i.elim0, some true, none⟩
      | none => ⟨0, fun i => i.elim0, some false, none⟩ }

/-- **The marker strip**. The timed conditional whose decider tests whether the second component of
the pair contains a `true`, whose positive branch is the private raw strip (copy the input, erase
its final `false` run and last `true`, replay), and whose negative branch outputs `[]`. -/
def stripLastTM : FinTM Bool :=
  timedCondTM (bufferedCompTM (pairExtractTM false true) anyTrueTM) rawStripTM (constTM [])

/-- The marker-existence scan halts within one more than the remaining length.
**Proof sketch.** False bits advance silently; a true or the right boundary
emits the corresponding verdict and halts. -/
private lemma anyTrue_run (x rest : List Bool) : ∀ pre (hx : x = pre ++ rest),
    ∃ t ≤ rest.length + 1,
      (anyTrueTM.tm.runFrom (scanCfg x (some ()) pre.length (by simp [hx]) []) t).state = none ∧
      (anyTrueTM.tm.runFrom (scanCfg x (some ()) pre.length (by simp [hx]) []) t).output =
        [rest.any id] := by
  induction rest with
  | nil =>
    intro pre hx
    refine ⟨1, by simp, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((anyTrueTM.tm.tr () _ _).apply _).state = none ∧ _
    rw [scanCfg_read]
    simp [hx, anyTrueTM, Action.apply, scanCfg]
  | cons b rest ih =>
    intro pre hx
    cases b with
    | true =>
      refine ⟨1, by simp, ?_⟩
      simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
      unfold MultiTapeTM.step
      change ((anyTrueTM.tm.tr () _ _).apply _).state = none ∧ _
      rw [scanCfg_read]
      simp [hx, anyTrueTM, Action.apply, scanCfg]
    | false =>
      have hs := scanStep_right anyTrueTM.tm x () (some ()) pre.length (by simp [hx]) [] none
        (by intro work; simp [hx, anyTrueTM])
      obtain ⟨t, ht, hh, ho⟩ := ih (pre ++ [false]) (by simpa [List.append_assoc] using hx)
      refine ⟨t + 1, by simp only [List.length_cons]; omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step, hs]
      simpa using And.intro hh ho

/-- The true-bit scanner starts at the first input cell and uses a linear bound. -/
private lemma anyTrue_computes : anyTrueTM.ComputesFunInTime
    (fun x => [x.any id]) (fun n => n + 1) := by
  intro x
  obtain ⟨t, ht, hs, ho⟩ := anyTrue_run x x [] rfl
  have hinit : anyTrueTM.tm.initCfg x = scanCfg x (some ()) 0 (by omega) [] := by
    apply Cfg.ext_zero_tapes <;> rfl
  have hc : anyTrueTM.ComputesInTime x [x.any id] t := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [hinit]
    exact ⟨hs, ho⟩
  exact hc.mono ht

/-- Marker absence is exactly the false verdict; a present marker can be
stripped after any fixed prefix without disturbing that prefix.
**Proof sketch.** Right induction follows `reverse.dropWhile`: append-false
preserves the previous result, and append-true selects the whole old word. -/
private lemma catalogMarker_cases (v : List Bool) :
    (v.any id = false ∧ splitAtLastTrue v = none) ∨
      ∃ u, v.any id = true ∧ splitAtLastTrue v = some u ∧
        ∀ pre, splitAtLastTrue (pre ++ v) = some (pre ++ u) := by
  induction v using List.reverseRecOn with
  | nil => left; simp [splitAtLastTrue]
  | append_singleton v b ih =>
    cases b with
    | false =>
      rcases ih with ⟨ha, hs⟩ | ⟨u, ha, hs, hp⟩
      · left; simpa [splitAtLastTrue] using And.intro ha hs
      · right
        refine ⟨u, by simpa using ha, by simpa [splitAtLastTrue] using hs, ?_⟩
        intro pre
        simpa [splitAtLastTrue, List.append_assoc] using hp pre
    | true =>
      right
      refine ⟨v, by simp, by simp [splitAtLastTrue], ?_⟩
      intro pre
      simp [splitAtLastTrue]

/-- The total suffix extractor never lengthens its input, including malformed
inputs, whose extracted suffix is empty. -/
private lemma catalogPayload_length (x : List Bool) :
    ((pairDecode x).map Prod.snd |>.getD []).length ≤ x.length := by
  cases hd : pairDecode x with
  | none => simp
  | some p =>
    rcases p with ⟨a, b⟩
    have hx := Turing.eq_pairEncode_of_pairDecode x a b hd
    simp only [Option.map_some, Option.getD_some]
    rw [hx]
    simp only [pairEncode, List.length_append]
    omega

/-- Run the given machine on the parsed payload, using the public relocated
composition engine and the payload's actual length. This is the quantitative
continuation interface for the threaded map; it does not yet emit the retained
first component or capture the transformed payload for that emission.
**Proof sketch.** The proved extractor validates and buffers before emission.
`bufferedComp_start` installs its suffix as virtual input; `bufferedSecondCfg_run`
simulates the payload machine with `bufferTape`/`virtualMove`. Charge its time
to `Tg |x|` using the nonexpanding suffix bound, not the extractor's larger
running-time bound. This distinction is necessary for arbitrary monotone `Tg`. -/
private lemma catalogPayload_computes {Mg : FinTM Bool}
    {g : List Bool → List Bool} {Tg : ℕ → ℕ}
    (hg : Mg.ComputesFunInTime g Tg) (hTg : Monotone Tg) :
    (bufferedCompTM (pairExtractTM false true) Mg).ComputesFunInTime
      (fun x => g ((pairDecode x).map Prod.snd |>.getD []))
      (fun n => 6 * (n + 1) + Tg n + 1) := by
  intro x
  let y := (pairDecode x).map Prod.snd |>.getD []
  have hF : (pairExtractTM false true).ComputesInTime x y (5 * (x.length + 1)) := by
    have hf := pairExtractTM_computes false true x
    cases hd : pairDecode x with
    | none => simpa [y, hd] using hf
    | some p => cases p; simpa [y, hd] using hf
  have hlen : y.length ≤ x.length := catalogPayload_length x
  obtain ⟨a, p, tapes, heads, ha, hstart⟩ :=
    bufferedComp_start (pairExtractTM false true) Mg x y (5 * (x.length + 1)) hF
  obtain ⟨b, _, hr⟩ := bufferedSecondCfg_run (pairExtractTM false true) Mg (Mg.tm.initCfg y) true
    (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads (Tg y.length)
  have hc := (computesInTime_iff _ _ _ _).mp (hg y)
  have hbase : (bufferedCompTM (pairExtractTM false true) Mg).ComputesInTime x (g y)
      (a + Tg y.length) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart, hr]
    exact ⟨by simpa only [bufferedSecondCfg, Option.map_eq_none_iff] using hc.1, hc.2⟩
  have htime : Tg y.length ≤ Tg x.length := hTg hlen
  exact hbase.mono (by dsimp only; omega)

/-- **P3, prepend a fixed word** (harvest: the HALT
batch's `prefixTM`/`prefixTM_computes`, whose promotion the batch formally
requested). Emitting the fixed word `w` and then copying the input is
computable in linear time; the constant may depend on `w`, which is fixed
before the machine.

**Construction sketch.** The fixed emission chain of
`Turing.FinTM.computesFunInTime_const` for `w`, then the one-state copy
scan of `Turing.FinTM.computesFunInTime_id`; the harvest source proves the
exact budget `|w| + |x| + 1`. -/
theorem computesFunInTime_prepend (w : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => w ++ x) fun n => c * (n + 1) := by
  refine ⟨prependTM w, w.length + 1, fun x => (prependTM_computes w x).mono ?_⟩
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

/-- **P4, input length in binary** (new; the unary
scan is a one-state sweep and the binary counter discipline is the
`Turing.incFixed` carry loop). The little-endian binary representation
`Nat.bits` of the input length is computable in linear time.

**Construction sketch.** One left-to-right input scan driving an in-place
binary counter on a work tape (the `Turing.incFixed` carry discipline, cost
amortized constant per input cell), then emit the counter word. -/
theorem computesFunInTime_lengthBits :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => Nat.bits x.length) fun n => c * (n + 1) := by
  obtain ⟨_, c, _, M, hM⟩ := Complexity.timeConstructible_id
  exact ⟨M, c, hM⟩

/-- **The unary generator's time**. The generator writes `C·(|x| + 1)^e` ones within
`(C + 5e + 4)·(n + 1)^e` steps: the sharp degree `e`, not the row's `e + 1`.

**Proof sketch.** For `e = 0`, `constTM_computes` gives `C + 1 ≤ C + 4` steps. For `e = d + 1`,
today's private `catalogPoly_unary_computes d C` is exactly the bound
`(C + 5(d + 1) + 4)·(n + 1)^(d + 1)`. This replaces Catalog's `f2_unary_sharp`, whose `e = 0` case
went through a linear allowance only because it reused the constant row's existential constant. -/
theorem polyUnaryTM_computes (C e : ℕ) :
    (polyUnaryTM C e).ComputesFunInTime
      (fun x => List.replicate (C * (x.length + 1) ^ e) true)
      (fun n => (C + 5 * e + 4) * (n + 1) ^ e) := by
  intro x
  cases e with
  | zero =>
    simp only [polyUnaryTM, pow_zero, Nat.mul_one]
    exact (constTM_computes (List.replicate C true) x).mono (by simp)
  | succ d => exact catalogPoly_unary_computes d C x

/-- **The unary generator's space**. At every time the generator has visited at most `5e·(|x| + 1)`
work cells.

**Proof sketch.** For `e = 0` there are no work tapes. For `e = d + 1`, `f2_poly_space`: the
startup lasts `2(|x| + 1)` steps from the origin, and the loop invariant confines every later
head to `[-1, |x| + 1]`, including after the halt; contain the visited images in the larger
interval and sum over the `d + 1` tapes. The number of loop iterations never appears. -/
theorem polyUnaryTM_spaceUsed (C e : ℕ) (x : List Bool) (t : ℕ) :
    (polyUnaryTM C e).tm.spaceUsed ((polyUnaryTM C e).tm.initCfg x) t ≤
      5 * e * (x.length + 1) := by
  sorry

/-- **P5, polynomial evaluation, unary clause**
(harvest: the TMSAT batch's `polyUnaryTM`/`poly_unary_computes`, proved with
budget `(C + 5(e+1) + 4)·(n+1)^(e+1)`). The exact unary value of
`C·(n+1)^e` at the input length is computable within a constant multiple of
`(n+1)^(e+1)`. Its instances are also the exact-emission primitive the
reduction constructions consume (catalog entry P7, subsumed here).

**Construction sketch** (indexing corrected per round-1 finding 5: the
harvest source's `poly_unary_computes` with loop parameter `c` emits
exponent `c + 1`, so this contract harvests with parameter `e - 1`): for
`e > 0`, `e` nested unary loop tapes of side length `n + 1`, installed by
one input scan, the innermost loop emitting `C` trues per box point —
exactly `C·(n+1)^e` in total; for `e = 0` the output is the constant
`List.replicate C true`, a fixed emission chain. A recursive invariant
restores completed inner heads, with loop depth `r` costing at most
`(C + 1 + 5r)·(n+1)^r`. -/
theorem computesFunInTime_polyUnary (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun x => List.replicate (C * (x.length + 1) ^ e) true)
        fun n => c * (n + 1) ^ (e + 1) := by
  cases e with
  | zero =>
    simpa using computesFunInTime_const (List.replicate C true)
  | succ d =>
    refine ⟨catalogPolyUnaryTM d C, C + 5 * (d + 1) + 4, fun x => ?_⟩
    apply (catalogPoly_unary_computes d C x).mono
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos x.length) (by omega))

/-- **The binary evaluator's time**. The evaluator computes `x ↦ Nat.bits (C·(|x| + 1)^e)` within
`(7C + 5e + 11)·(n + 1)^e` steps.

**Proof sketch.** If `C = 0` or `e = 0`, the constant machine of the answer takes
`|Nat.bits C| + 1 ≤ C + 1` steps (`Turing.length_bits_le_self`). Otherwise the buffered
composition takes the generator's `(C + 5e + 4)·P` steps, `P = (n + 1)^e`, plus the
intermediate's length `C·P` and `2`, plus the counter's `5·(C·P + 1)`, in all
`(7C + 5e + 4)·P + 7 ≤ (7C + 5e + 11)·P` (`bufferedCompTM_computesInTime`). -/
theorem polyBitsTM_computes (C e : ℕ) :
    (polyBitsTM C e).ComputesFunInTime (fun x => Nat.bits (C * (x.length + 1) ^ e))
      (fun n => (7 * C + 5 * e + 11) * (n + 1) ^ e) := by
  intro x
  have hp : 1 ≤ (x.length + 1) ^ e := Nat.one_le_pow _ _ (Nat.succ_pos _)
  by_cases hC : C = 0
  · subst hC
    simp only [polyBitsTM, if_true, Nat.zero_mul]
    refine (constTM_computes (Nat.bits 0) x).mono ?_
    rw [Nat.zero_bits, List.length_nil]
    exact Nat.mul_pos (by omega) hp
  · cases e with
    | zero =>
      simp only [polyBitsTM, hC, if_false, pow_zero, Nat.mul_one]
      refine (constTM_computes (Nat.bits C) x).mono ?_
      have := Turing.length_bits_le_self C
      omega
    | succ d =>
      simp only [polyBitsTM, hC, if_false]
      have h := bufferedCompTM_computesInTime (polyUnaryTM C (d + 1)) lengthBitsTM
        (polyUnaryTM_computes C (d + 1) x)
        (lengthBitsTM_computes (List.replicate (C * (x.length + 1) ^ (d + 1)) true))
      simp only [List.length_replicate] at h
      refine h.mono ?_
      dsimp only
      generalize (x.length + 1) ^ (d + 1) = P at hp ⊢
      calc (C + 5 * (d + 1) + 4) * P + C * P + 2 + 5 * (C * P + 1)
          = (7 * C + 5 * (d + 1) + 4) * P + 7 := by ring
        _ ≤ (7 * C + 5 * (d + 1) + 4) * P + 7 * P := by omega
        _ = (7 * C + 5 * (d + 1) + 11) * P := by ring

/-- **P5, polynomial evaluation, binary clause**
(harvest: the TMSAT batch's composition of the unary generator with the
binary length counter). The little-endian binary representation of
`C·(n+1)^e` at the input length is computable within a constant multiple
of `(n+1)^(e+1)`.

**Construction sketch.** The unary generator above composed with the
binary length counter of `computesFunInTime_lengthBits` through the public
buffered composition (`Turing.FinTM.computesFunInTime_comp`) — the harvest
source's exact route, under the same `e - 1` harvest-indexing convention
as the unary clause (round-1 finding 5). -/
theorem computesFunInTime_polyBits (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => Nat.bits (C * (x.length + 1) ^ e))
        fun n => c * (n + 1) ^ (e + 1) := by
  obtain ⟨U, a, hU⟩ := computesFunInTime_polyUnary C e
  obtain ⟨B, b, hB⟩ := computesFunInTime_lengthBits
  obtain ⟨M, d, hM⟩ := computesFunInTime_comp hU hB
    (by intro m n h; exact Nat.mul_le_mul_left b (Nat.add_le_add_right h 1))
  refine ⟨M, d * (a + 1) * (b + 1), fun x => ?_⟩
  have hm := hM x
  simp only [Function.comp_apply, List.length_replicate] at hm
  apply hm.mono
  let P := (x.length + 1) ^ (e + 1)
  have hp : 1 ≤ P := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hb : b + 1 ≤ (b + 1) * P := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (b + 1) hp
  have hbound : a * P + b * (a * P + 1) + 1 ≤ (a + 1) * (b + 1) * P := by
    calc
      _ = a * (b + 1) * P + (b + 1) := by ring
      _ ≤ a * (b + 1) * P + (b + 1) * P := Nat.add_le_add_left hb _
      _ = _ := by ring
  calc
    _ ≤ d * ((a + 1) * (b + 1) * P) := Nat.mul_le_mul_left d hbound
    _ = _ := by ring

/-- **P6, pairing with a fixed first component**
(harvest: the HALT batch's `fixedPair_computes`, proved with the exact
budget `2|α| + |x| + 3`; its promotion was formally requested). For a
fixed word `α`, the self-delimiting pairing `pairEncode α x` is computable
in linear time. This is the threading stage: downstream threaded contracts
receive `pairEncode a b` and act on `b` while carrying `a`.

**Construction sketch.** `pairEncode α x` is literally
`(α doubled) ++ [false, true] ++ x`, so this is the prepend primitive at
that fixed word; it is kept as its own contract because consumers cite the
pairing grammar, and the harvest source proves the exact budget
`2|α| + |x| + 3`. -/
theorem computesFunInTime_pairEncodeFixed (α : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => pairEncode α x) fun n => c * (n + 1) := by
  simpa only [pairEncode] using
    computesFunInTime_prepend ((α.flatMap fun b => [b, b]) ++ [false, true])

/-- **P6, first-component extraction** (new; the
aligned two-bit scan of the `Turing.pairDecode` grammar as a machine). On
a well-formed pair the doubled prefix is undoubled and emitted; on a
malformed input the output is `[]`.

**Construction sketch.** Output is append-only, so the scan must not emit
before the parse succeeds: undouble aligned `00`/`11` blocks onto a work
tape until the aligned `01` separator, then replay the buffer to the
output; any misaligned block halts with nothing emitted. -/
theorem computesFunInTime_pairFst :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => ((pairDecode x).map Prod.fst).getD [])
        fun n => c * (n + 1) := by
  refine ⟨pairExtractTM true false, 5, fun x => ?_⟩
  have h := pairExtractTM_computes true false x
  cases hd : pairDecode x with
  | none => simpa [hd] using h
  | some p => cases p; simpa [hd] using h

/-- **P6, second-component extraction** (new; the
same aligned scan, emitting the suffix after the separator instead). On a
malformed input the output is `[]`. Iterating this extractor is how the
nested-quadruple parsers of the TMSAT constructions decompose.

**Construction sketch.** Scan aligned blocks without emitting until the
separator is found (validity of the prefix must be known before any suffix
bit may be emitted), then copy the suffix verbatim; a misaligned block
halts silently. -/
theorem computesFunInTime_pairSnd :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => ((pairDecode x).map Prod.snd).getD [])
        fun n => c * (n + 1) := by
  refine ⟨pairExtractTM false true, 5, fun x => ?_⟩
  have h := pairExtractTM_computes false true x
  cases hd : pairDecode x with
  | none => simpa [hd] using h
  | some p => cases p; simpa [hd] using h

/-- **P6, grammar validity** (new). The single-bit
test for membership in the `Turing.pairDecode` grammar, the guard stage
every parser pipeline rejects malformed inputs with.

**Construction sketch.** One aligned two-bit scan in finite control; emit
the single verdict bit at the separator or at the first misaligned block.
No buffering is needed — only one bit is ever emitted, at the end. -/
theorem computesFunInTime_pairValid :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => [(pairDecode x).isSome])
        fun n => c * (n + 1) := by
  exact ⟨pairValidTM, 1, fun x => by simpa using pairValidTM_computes x⟩

/-- **P13, pair to concatenation** (round-2 addition
per round-1 finding 3 — the D-WRAP obligation's exact shape). On
`pairEncode x u`, emit `x ++ u`; malformed inputs yield `[]`, the threaded
rejection the downstream guard reads (the reduction wrapper's own
`[false]` rejection is assembled at the decider stage).

**Construction sketch.** Undouble the aligned prefix onto a work tape —
nothing emitted while validity is unknown; at the aligned separator,
replay the buffered first component and then copy the suffix verbatim; a
misaligned block halts with nothing emitted. -/
theorem computesFunInTime_pairConcat :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun z => match pairDecode z with
          | some (a, b) => a ++ b
          | none => [])
        fun n => c * (n + 1) := by
  refine ⟨pairExtractTM true true, 5, fun x => ?_⟩
  have h := pairExtractTM_computes true true x
  cases hd : pairDecode x with
  | none => simpa [hd] using h
  | some p => cases p; simpa [hd] using h

/-- **P14, duplication into a pair** (round-2 addition
per round-1 finding 3 — the entry stage of data-retaining pipelines:
the reduction emitter retains `x` while its duplicate feeds the generated
components). Emit `pairEncode x x`.

**Construction sketch.** Two input passes: emit each read bit doubled,
then the separator, then copy the input verbatim. No buffering is needed
— the pairing prefix is valid bit by bit, and every input is legal. -/
theorem computesFunInTime_pairDup :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => pairEncode x x) fun n => c * (n + 1) := by
  exact ⟨pairDupTM, 4, pairDup_computes⟩

/-- The threaded-map controller uses the last tape only for captured output;
all administrative actions preserve its contents and the source bank. -/
private def mapAction (M : FinTM Bool) (m d : SignType) (b : Option Bool)
    (q : Option (M.State ⊕ (Fin 7 ⊕ (Bool × Option Bool)))) :
    Action (M.k + 1) Bool (M.State ⊕ (Fin 7 ⊕ (Bool × Option Bool))) :=
  ⟨m, fun i => (none, if i.val < M.k then 0 else d), b, q⟩

/-- Capture the payload computation, rewind both relevant heads, and silently
validate the original pair. Only after validation, replay the native encoded
prefix followed by the captured payload. The source bank is never reused. -/
private def pairMapTM (M : FinTM Bool) : FinTM Bool where
  k := M.k + 1
  State := M.State ⊕ (Fin 7 ⊕ (Bool × Option Bool))
  tm := {
    q₀ := .inl M.tm.q₀
    tr := fun q inp work => match q with
      | .inl s => captureAction Sum.inl (.inr (.inl 0))
          (M.tm.tr s inp fun i => work i.castSucc)
      | .inr (.inl q) => match q.val with
        | 0 => mapAction M 0 .neg none (some (.inr (.inl 1)))
        | 1 => match work (Fin.last M.k) with
          | some _ => mapAction M 0 .neg none (some (.inr (.inl 1)))
          | none => mapAction M 0 .pos none (some (.inr (.inl 2)))
        | 2 => controlAction .neg (some (.inr (.inl 3)))
        | 3 => match inp with
          | some _ => controlAction .neg (some (.inr (.inl 3)))
          | none => controlAction .pos (some (.inr (.inr (false, none))))
        | 4 => controlAction .neg (some (.inr (.inl 5)))
        | 5 => match inp with
          | some _ => controlAction .neg (some (.inr (.inl 5)))
          | none => controlAction .pos (some (.inr (.inr (true, none))))
        | _ => match work (Fin.last M.k) with
          | some b => mapAction M 0 .pos (some b) (some (.inr (.inl 6)))
          | none => mapAction M 0 0 none none
      | .inr (.inr (emit, none)) => match inp with
        | none => mapAction M 0 0 none none
        | some b => mapAction M .pos 0 (if emit then some b else none)
            (some (.inr (.inr (emit, some b))))
      | .inr (.inr (emit, some b)) => match inp with
        | none => mapAction M 0 0 none none
        | some d => mapAction M .pos 0 (if emit then some d else none)
            (if b = d then some (.inr (.inr (emit, none)))
             else if b then none
             else some (.inr (.inl (if emit then 6 else 4)))) }

/-- An administrative configuration preserves the completed source bank and
captured word, while exposing the input and capture-head positions. -/
private def mapCfg (M : FinTM Bool) {x : List Bool} (c : Cfg M.k Bool M.State x)
    (q : Option (pairMapTM M).State) (p : Fin (x.length + 2)) (h : ℤ)
    (out : List Bool) : Cfg (M.k + 1) Bool (pairMapTM M).State x :=
  { captureCfg (fun s : M.State => (Sum.inl s : (pairMapTM M).State))
      (.inr (.inl 0)) [] out c with
    state := q
    inputPos := p
    workTapePos := fun j => if hj : j.val < M.k then c.workTapePos ⟨j, hj⟩ else h }

/-- Administrative steps change only the named heads, control, and optional
output. No work-tape cell is written. -/
private lemma mapAction_apply (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (q q' : Option (pairMapTM M).State)
    (p : Fin (x.length + 2)) (h : ℤ) (out : List Bool)
    (m d : SignType) (b : Option Bool) :
    (mapAction M m d b q').apply (mapCfg M c q p h out) =
      mapCfg M c q' (moveInputPos p m) (h + d.cast) (out ++ b.toList) := by
  refine Cfg.ext rfl rfl rfl ?_ rfl
  funext j
  by_cases hj : j.val < M.k <;> simp [mapAction, mapCfg, Action.apply, hj]

/-- Rewinding the captured word from its final cell costs its length plus one.
**Proof sketch.** At the left blank, move right to the input-rewind phase.
Otherwise a single silent left step reduces the remaining prefix length. -/
private lemma mapBuffer_rewind (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (p : Fin (x.length + 2)) :
    ∀ j, j ≤ c.output.length →
    (pairMapTM M).tm.runFrom
      (mapCfg M c (some (.inr (.inl 1))) p ((j : ℤ) - 1) []) (j + 1) =
      mapCfg M c (some (.inr (.inl 2))) p 0 [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    simp only [pairMapTM, mapCfg, captureCfg, Cfg.workTapeSymbols, Fin.val_last,
      Nat.lt_irrefl, ↓reduceDIte, Nat.cast_zero, zero_sub, List.nil_append, bufferTape_left]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero _
    · rfl
    · funext i; by_cases hi : i.val < M.k <;> simp [mapAction, Action.apply, hi]
    · rfl
  | succ j ih =>
    intro hj
    have hs : (pairMapTM M).tm.step
        (mapCfg M c (some (.inr (.inl 1))) p (((j + 1 : ℕ) : ℤ) - 1) []) =
        mapCfg M c (some (.inr (.inl 1))) p ((j : ℤ) - 1) [] := by
      have hz : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [hz]
      unfold MultiTapeTM.step
      change ((pairMapTM M).tm.tr (.inr (.inl 1)) _ _).apply _ = _
      have hw : (mapCfg M c (some (.inr (.inl 1))) p j []).workTapeSymbols
          (Fin.last M.k) = some (c.output[j]'(by omega)) := by
        simp [mapCfg, captureCfg, Cfg.workTapeSymbols,
          List.getElem?_eq_getElem (by omega : j < c.output.length)]
      simp only [pairMapTM, hw]
      rw [mapAction_apply]
      simp [SignType.cast, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Capture and rewind reach the silent validator with physical output empty.
**Proof sketch.** The least source halt supplies the capture guard. Rewind the
captured word, then the input, preserving every completed source tape. -/
private lemma mapStart (M : FinTM Bool) (x w : List Bool) (T : ℕ)
    (hM : M.ComputesInTime x w T) :
    ∃ t ≤ T + w.length + x.length + 5, ∃ c : Cfg M.k Bool M.State x,
      c.output = w ∧
      (pairMapTM M).tm.runFrom ((pairMapTM M).tm.initCfg x) t =
        mapCfg M c (some (.inr (.inr (false, none)))) 1 0 [] := by
  classical
  have hh : ∃ t, (M.tm.runFrom (M.tm.initCfg x) t).state = none :=
    ⟨T, ((computesInTime_iff _ _ _ _).mp hM).1⟩
  let t := Nat.find hh
  let c := M.tm.runFrom (M.tm.initCfg x) t
  have ht : t ≤ T := Nat.find_min' hh ((computesInTime_iff _ _ _ _).mp hM).1
  have hs : c.state = none := Nat.find_spec hh
  have hc : M.ComputesInTime x c.output t := (computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
  have ho : c.output = w := hc.output_unique hM
  let emb : M.State → (pairMapTM M).State := Sum.inl
  let ret : (pairMapTM M).State := .inr (.inl 0)
  have hinit : (pairMapTM M).tm.initCfg x = captureCfg emb ret [] [] (M.tm.initCfg x) := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i; simp [captureCfg, MultiTapeTM.initCfg, Cfg.init]
    · funext i; simp [captureCfg, MultiTapeTM.initCfg, Cfg.init]
  have hcap : (pairMapTM M).tm.runFrom ((pairMapTM M).tm.initCfg x) t =
      captureCfg emb ret [] [] c := by
    rw [hinit]
    exact capture_run M.tm (pairMapTM M).tm emb ret (fun _ _ _ => rfl)
      [] [] _ t (fun s hst => Nat.find_min hh hst)
  have hback : (pairMapTM M).tm.step (captureCfg emb ret [] [] c) =
      mapCfg M c (some (.inr (.inl 1))) c.inputPos (c.output.length - 1) [] := by
    have hstate : (captureCfg emb ret [] [] c).state = some ret := by simp [captureCfg, hs]
    simp only [MultiTapeTM.step, hstate]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i
    by_cases hi : i.val < M.k <;>
      simp [pairMapTM, ret, mapAction, Action.apply, captureCfg, mapCfg, hi, sub_eq_add_neg]
  obtain ⟨r, hrle, hr⟩ := catalogRewind (pairMapTM M).tm
    (.inr (.inl 2)) (.inr (.inl 3)) (some (.inr (.inr (false, none))))
    (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl)
    (mapCfg M c (some (.inr (.inl 2))) c.inputPos 0 []) rfl
  have hlen : c.output.length = w.length := congrArg List.length ho
  have hfirst : (pairMapTM M).tm.runFrom ((pairMapTM M).tm.initCfg x) (t + 1) =
      mapCfg M c (some (.inr (.inl 1))) c.inputPos (c.output.length - 1) [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hcap, hback]
  refine ⟨t + 1 + (c.output.length + 1) + r, ?_, c, ho, ?_⟩
  · change r ≤ c.inputPos.val + 2 at hrle
    have := c.inputPos.isLt
    omega
  · rw [MultiTapeTM.runFrom_add _ _ r,
      MultiTapeTM.runFrom_add _ (t + 1) (c.output.length + 1), hfirst,
      mapBuffer_rewind M c c.inputPos c.output.length (le_refl _), hr]
    rfl

/-- The parser and prefix-replay phases read the indexed native input cell. -/
private lemma mapCfg_read (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (q : Option (pairMapTM M).State)
    (i : ℕ) (hi : i ≤ x.length) (h : ℤ) (out : List Bool) :
    (mapCfg M c q ⟨i + 1, by omega⟩ h out).inputSymbol = x[i]? :=
  inputSymbol_at _ i hi rfl

/-- One aligned-block read remembers its first bit. Only the replay phase
emits it; the validator remains silent. -/
private lemma mapParse_first (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (pre rest out : List Bool) (b emit : Bool)
    (hx : x = pre ++ b :: rest) :
    (pairMapTM M).tm.step
      (mapCfg M c (some (.inr (.inr (emit, none)))) ⟨pre.length + 1, by simp [hx] <;> omega⟩ 0 out) =
      mapCfg M c (some (.inr (.inr (emit, some b))))
        ⟨pre.length + 2, by simp [hx] <;> omega⟩ 0 (out ++ if emit then [b] else []) := by
  unfold MultiTapeTM.step
  change ((pairMapTM M).tm.tr (.inr (.inr (emit, none))) _ _).apply _ = _
  rw [mapCfg_read M c _ pre.length (by simp [hx])]
  have hin : x[pre.length]? = some b := by simp [hx]
  simp only [pairMapTM, hin]
  rw [mapAction_apply, moveInputPos_pos_of_ne_right _ (by simp [hx] <;> omega)]
  cases emit <;> rfl

/-- A two-bit block either continues parsing, rejects `10`, or selects the
post-separator phase. The captured payload and its origin head are preserved. -/
private lemma mapParse_block (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (pre rest out : List Bool) (b d emit : Bool)
    (hx : x = pre ++ b :: d :: rest) :
    (pairMapTM M).tm.runFrom
      (mapCfg M c (some (.inr (.inr (emit, none))))
        ⟨pre.length + 1, by simp [hx] <;> omega⟩ 0 out) 2 =
      mapCfg M c
        (if b = d then some (.inr (.inr (emit, none))) else if b then none
          else some (.inr (.inl (if emit then 6 else 4))))
        ⟨pre.length + 3, by simp [hx] <;> omega⟩ 0 (out ++ if emit then [b, d] else []) := by
  change (pairMapTM M).tm.step ((pairMapTM M).tm.step _) = _
  rw [mapParse_first M c pre (d :: rest) out b emit hx]
  unfold MultiTapeTM.step
  change ((pairMapTM M).tm.tr (.inr (.inr (emit, some b))) _ _).apply _ = _
  rw [mapCfg_read M c _ (pre.length + 1) (by simp [hx])]
  have hin : x[pre.length + 1]? = some d := by simp [hx]
  simp only [pairMapTM, hin]
  rw [mapAction_apply, moveInputPos_pos_of_ne_right _ (by simp [hx] <;> omega)]
  cases emit <;> simp [SignType.cast, List.append_assoc]

/-- The silent aligned validator either halts without output or reaches the
input-rewind seam. Its total cost is at most the unread length plus one.
**Proof sketch.** Induction over aligned two-bit blocks. Equal bits recurse,
`01` validates, and `10`, a missing separator, or an incomplete block rejects. -/
private lemma mapValidate (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (rest : List Bool) :
    ∀ pre (hx : x = pre ++ rest), ∃ t ≤ rest.length + 1,
      if (pairDecode rest).isSome then
        ∃ p, (pairMapTM M).tm.runFrom
          (mapCfg M c (some (.inr (.inr (false, none))))
            ⟨pre.length + 1, by simp [hx] <;> omega⟩ 0 []) t =
          mapCfg M c (some (.inr (.inl 4))) p 0 []
      else
        ((pairMapTM M).tm.runFrom
          (mapCfg M c (some (.inr (.inr (false, none))))
            ⟨pre.length + 1, by simp [hx] <;> omega⟩ 0 []) t).state = none ∧
        ((pairMapTM M).tm.runFrom
          (mapCfg M c (some (.inr (.inr (false, none))))
            ⟨pre.length + 1, by simp [hx] <;> omega⟩ 0 []) t).output = [] := by
  induction rest using List.twoStepInduction with
  | nil =>
    intro pre hx
    refine ⟨1, by simp, ?_⟩
    simp only [pairDecode, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
      MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (((pairMapTM M).tm.tr (.inr (.inr (false, none))) _ _).apply _).state = none ∧ _
    rw [mapCfg_read M c _ pre.length (by simp [hx])]
    simp [hx, pairMapTM, mapAction, Action.apply, mapCfg, captureCfg]
  | singleton b =>
    intro pre hx
    refine ⟨2, by simp, ?_⟩
    have hd : pairDecode [b] = none := by cases b <;> rfl
    simp only [hd, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    rw [mapParse_first M c pre [] [] b false hx]
    unfold MultiTapeTM.step
    change (((pairMapTM M).tm.tr (.inr (.inr (false, some b))) _ _).apply _).state = none ∧ _
    rw [mapCfg_read M c _ (pre.length + 1) (by simp [hx])]
    simp [hx, pairMapTM, mapAction, Action.apply, mapCfg, captureCfg]
  | cons_cons b d rest ih _ =>
    intro pre hx
    by_cases h : b = d
    · subst d
      obtain ⟨t, ht, hh⟩ := ih (pre ++ [b, b]) (by simpa [List.append_assoc] using hx)
      refine ⟨2 + t, by simp only [List.length_cons]; omega, ?_⟩
      rw [MultiTapeTM.runFrom_add, mapParse_block M c pre rest [] b b false hx]
      simp only [↓reduceIte, List.append_nil]
      have hp : (pairDecode (b :: b :: rest)).isSome = (pairDecode rest).isSome := by
        cases b <;> simp [pairDecode]
      rw [hp]
      simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero,
        show pre.length + 2 + 1 = pre.length + 3 by omega] using hh
    · cases b <;> cases d
      · exact False.elim (h rfl)
      · refine ⟨2, by simp, ?_⟩
        simp only [pairDecode, Option.isSome_some, ↓reduceIte]
        refine ⟨⟨pre.length + 3, by simp [hx] <;> omega⟩, ?_⟩
        rw [mapParse_block M c pre rest [] false true false hx]
        rfl
      · refine ⟨2, by simp, ?_⟩
        simp only [pairDecode, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
        rw [mapParse_block M c pre rest [] true false false hx]
        exact ⟨rfl, rfl⟩
      · exact False.elim (h rfl)

/-- Once validation has succeeded, replay precisely the encoded prefix and
separator and enter the captured-payload replay with its head still at zero.
**Proof sketch.** Induct on the decoded first component. Each doubled bit
costs two emitting steps; the final `01` costs two and switches replay tapes. -/
private lemma mapPrefix_replay (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (a b : List Bool) :
    ∀ pre out (hx : x = pre ++ pairEncode a b), ∃ p,
    (pairMapTM M).tm.runFrom
      (mapCfg M c (some (.inr (.inr (true, none))))
        ⟨pre.length + 1, by simp [hx, pairEncode]; omega⟩ 0 out) (2 * a.length + 2) =
      mapCfg M c (some (.inr (.inl 6))) p 0 (out ++ pairEncode a []) := by
  induction a with
  | nil =>
    intro pre out hx
    have hx' : x = pre ++ false :: true :: b := by simpa [pairEncode] using hx
    refine ⟨⟨pre.length + 3, by simp [hx'] <;> omega⟩, ?_⟩
    simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add] using
      mapParse_block M c pre b out false true true hx'
  | cons bit a ih =>
    intro pre out hx
    have hx' : x = pre ++ bit :: bit :: pairEncode a b := by
      simpa [pairEncode, List.append_assoc] using hx
    obtain ⟨p, hp⟩ := ih (pre ++ [bit, bit]) (out ++ [bit, bit])
      (by simpa [List.append_assoc] using hx')
    refine ⟨p, ?_⟩
    rw [show 2 * (bit :: a).length + 2 = 2 + (2 * a.length + 2) by simp; omega,
      MultiTapeTM.runFrom_add, mapParse_block M c pre (pairEncode a b) out bit bit true hx']
    simp only [↓reduceIte]
    simpa [pairEncode, List.append_assoc] using hp

/-- Captured-payload replay preserves the bank and emits each stored cell once.
**Proof sketch.** Induct over emitted cells, using `take_succ` and the contiguous
buffer read equation. The terminal blank supplies the final silent halt. -/
private lemma mapPayload_replay (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (p : Fin (x.length + 2)) (out : List Bool) :
    ∀ j (_hj : j ≤ c.output.length),
    (pairMapTM M).tm.runFrom
      (mapCfg M c (some (.inr (.inl 6))) p 0 out) j =
      mapCfg M c (some (.inr (.inl 6))) p j (out ++ c.output.take j) := by
  intro j
  induction j with
  | zero => intro hj; simp [mapCfg]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    unfold MultiTapeTM.step
    change ((pairMapTM M).tm.tr (.inr (.inl 6)) _ _).apply _ = _
    have hw : (mapCfg M c (some (.inr (.inl 6))) p j
        (out ++ c.output.take j)).workTapeSymbols (Fin.last M.k) =
          some (c.output[j]'(by omega)) := by
      simp [mapCfg, captureCfg, Cfg.workTapeSymbols,
        List.getElem?_eq_getElem (by omega : j < c.output.length)]
    simp only [pairMapTM, hw]
    rw [mapAction_apply]
    rw [moveInputPos_zero, List.take_succ,
      List.getElem?_eq_getElem (by omega : j < c.output.length)]
    simp only [SignType.cast, Nat.cast_add, Nat.cast_one, Option.toList_some,
      List.append_assoc]

/-- The last blank-reading step halts after the entire capture has been emitted. -/
private lemma mapPayload_finish (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (p : Fin (x.length + 2)) (out : List Bool) :
    ((pairMapTM M).tm.runFrom
      (mapCfg M c (some (.inr (.inl 6))) p 0 out) (c.output.length + 1)).state = none ∧
    ((pairMapTM M).tm.runFrom
      (mapCfg M c (some (.inr (.inl 6))) p 0 out) (c.output.length + 1)).output = out ++ c.output := by
  rw [MultiTapeTM.runFrom_succ_eq_step', mapPayload_replay M c p out _ (le_refl _)]
  simp [MultiTapeTM.step, pairMapTM, mapCfg, captureCfg, Cfg.workTapeSymbols,
    mapAction, Action.apply]

/-- The complete controller retains the first component and appends the
source's captured result, rejecting malformed inputs without any emission.
**Proof sketch.** Concatenate capture/rewind, silent validation, input rewind,
encoded-prefix replay, and captured-payload replay. Source output length is
at most its running time. The two replay lengths and all input scans therefore
fit `4 (T(n) + n + 3)`; no running time is evaluated at a padded input length. -/
private lemma pairMap_computes_at {M : FinTM Bool} {x y : List Bool} {time : ℕ}
    (hM : M.ComputesInTime x y time) :
    (pairMapTM M).ComputesInTime x
      (match pairDecode x with
        | some (a, _) => pairEncode a y
        | none => []) (4 * (time + x.length + 3)) := by
  have hlen : y.length ≤ time := by
    have hout := ((computesInTime_iff _ _ _ _).mp hM).2
    simpa only [hout] using M.tm.output_length_le x (time)
  obtain ⟨t, ht, c, ho, hstart⟩ := mapStart M x y (time) hM
  obtain ⟨u, hu, hval⟩ := mapValidate M c x [] (by simp)
  simp only [List.length_nil, Nat.zero_add] at hval
  have hpos : (⟨1, by omega⟩ : Fin (x.length + 2)) = 1 := by
    apply Fin.ext
    simp
  rw [hpos] at hval
  have hclen : c.output.length = y.length := congrArg List.length ho
  cases hd : pairDecode x with
  | none =>
    simp only [hd, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hval ⊢
    have hc : (pairMapTM M).ComputesInTime x [] (t + u) := by
      apply (computesInTime_iff _ _ _ _).mpr
      rw [MultiTapeTM.runFrom_add, hstart]
      exact hval
    exact hc.mono (by omega)
  | some ab =>
    rcases ab with ⟨a, b⟩
    simp only [hd, Option.isSome_some, ↓reduceIte] at hval ⊢
    obtain ⟨p, hp⟩ := hval
    obtain ⟨r, hrle, hr⟩ := catalogRewind (pairMapTM M).tm
      (.inr (.inl 4)) (.inr (.inl 5)) (some (.inr (.inr (true, none))))
      (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl)
      (mapCfg M c (some (.inr (.inl 4))) p 0 []) rfl
    have hr' : (pairMapTM M).tm.runFrom
        (mapCfg M c (some (.inr (.inl 4))) p 0 []) r =
        mapCfg M c (some (.inr (.inr (true, none)))) 1 0 [] := hr
    obtain ⟨p', hp'⟩ := mapPrefix_replay M c a b [] []
      (by simpa using Turing.eq_pairEncode_of_pairDecode x a b hd)
    simp only [List.length_nil, Nat.zero_add, List.nil_append] at hp'
    rw [hpos] at hp'
    have hprefix : (pairMapTM M).tm.runFrom ((pairMapTM M).tm.initCfg x)
        ((t + u + r) + (2 * a.length + 2)) =
        mapCfg M c (some (.inr (.inl 6))) p' 0 (pairEncode a []) := by
      rw [MultiTapeTM.runFrom_add _ _ (2 * a.length + 2),
        MultiTapeTM.runFrom_add _ _ r, MultiTapeTM.runFrom_add _ t u,
        hstart, hp, hr', hp']
    have hc : (pairMapTM M).ComputesInTime x (pairEncode a y)
        (((t + u + r) + (2 * a.length + 2)) + (c.output.length + 1)) := by
      apply (computesInTime_iff _ _ _ _).mpr
      rw [MultiTapeTM.runFrom_add _ _ (c.output.length + 1), hprefix]
      obtain ⟨hs, hout⟩ := mapPayload_finish M c p' (pairEncode a [])
      refine ⟨hs, ?_⟩
      simpa only [ho, pairEncode_eq, List.append_assoc] using hout
    apply hc.mono
    have hpbound := p.isLt
    change r ≤ p.val + 2 at hrle
    have hxlen : x.length = 2 * a.length + 2 + b.length := by
      rw [Turing.eq_pairEncode_of_pairDecode x a b hd, Turing.length_pairEncode]
    omega

/-- The threaded map's total contract from a bound on each source activation. -/
private lemma pairMap_computes {M : FinTM Bool} {f : List Bool → List Bool}
    {T : ℕ → ℕ} (hM : M.ComputesFunInTime f T) :
    (pairMapTM M).ComputesFunInTime
      (fun x => match pairDecode x with
        | some (a, _) => pairEncode a (f x)
        | none => []) (fun n => 4 * (T n + n + 3)) :=
  (computesFunInTime_iff _ _ _).2 fun x =>
    pairMap_computes_at ((computesFunInTime_iff _ _ _).1 hM x)

/-- On a pair, a threaded map can charge the actual time of the payload machine.
For each computation sending `b` to `y` in `time` steps, the same wrapper
sends `⟨a,b⟩` to `⟨a,y⟩` in at most `40 (time + |⟨a,b⟩| + 1)` steps.

**Proof sketch.** The pair reader extracts the payload. Buffered composition
runs the supplied computation on that payload. The existing threaded map
retains the prefix and emits the captured result. Both encoding passes and
the rewind are linear in the pair and captured output lengths. -/
theorem exists_pairMapSnd_computesInTime (G : FinTM Bool) :
    ∃ M : FinTM Bool, ∀ (a b y : List Bool) (time : ℕ), G.ComputesInTime b y time →
      M.ComputesInTime (pairEncode a b) (pairEncode a y)
        (40 * (time + (pairEncode a b).length + 1)) := by
  refine ⟨pairMapTM (bufferedCompTM (pairExtractTM false true) G), fun a b y time hg => ?_⟩
  have hb : (pairExtractTM false true).ComputesInTime (pairEncode a b) b
      (5 * ((pairEncode a b).length + 1)) := by
    simpa only [pairDecode_pairEncode, Bool.false_eq_true, ↓reduceIte, List.nil_append] using
      pairExtractTM_computes false true (pairEncode a b)
  have hcall := bufferedCompTM_computesInTime (pairExtractTM false true) G hb hg
  have hmap := pairMap_computes_at hcall
  rw [pairDecode_pairEncode] at hmap
  exact hmap.mono (by rw [length_pairEncode]; omega)

/-- **C1, the threaded map combinator** (round-2
addition per round-1 finding 3 — the data-retaining assembly the
extractors deliberately do not provide: sequential composition yields
`g (f z)` only, never simultaneous access to a retained component). Given
a machine for `g`, transform a pair's payload while carrying its head
component unchanged; malformed inputs yield `[]`. Monotonicity of `Tg`
converts the payload-length bound `|b| ≤ |z|` into a time bound, exactly
as in `Turing.FinTM.computesFunInTime_comp`.

**Construction sketch.** Parse `pairEncode a b` onto two work tapes,
silent until the separator validates; run the `g`-machine on `b`
relocated-and-captured (the W1 discipline — its output lands on the
capture tape, with length bounded by its running time via
`Turing.MultiTapeTM.output_length_le`); then emit the re-encoded pair:
doubled `a`, separator, captured `g b`. -/
theorem computesFunInTime_pairMapSnd {Mg : FinTM Bool}
    {g : List Bool → List Bool} {Tg : ℕ → ℕ}
    (hg : Mg.ComputesFunInTime g Tg) (hTg : Monotone Tg) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun z => match pairDecode z with
          | some (a, b) => pairEncode a (g b)
          | none => [])
        fun n => c * (n + 1 + Tg n) := by
  have hM := pairMap_computes (catalogPayload_computes hg hTg)
  refine ⟨pairMapTM (bufferedCompTM (pairExtractTM false true) Mg), 40, fun x => ?_⟩
  have hc := hM x
  have heq : (match pairDecode x with
      | some (a, _) => pairEncode a (g ((pairDecode x).map Prod.snd |>.getD []))
      | none => []) = (match pairDecode x with
      | some (a, b) => pairEncode a (g b)
      | none => []) := by
    cases hd : pairDecode x with
    | none => rfl
    | some ab => cases ab; simp
  dsimp only at hc
  rw [heq] at hc
  exact hc.mono (by dsimp only; omega)

/-- **The threaded length check's time**. On `pairEncode a b` the check outputs
`[decide (|b| ≤ C·(|a| + 1)^e)]`, and `[false]` on a malformed input, within
`(C + 5e + 17)·((n + 1)^e + n + 1)` steps.

**Proof sketch.** The time half of Catalog's `computesFunInTime_pairLenCheck_spaceUsed`, over the
named witness: the decoded first component has length at most `n` (Catalog's `f2_first_length`,
moved), so the buffered composition costs
`5(n + 1) + n + 2 + (C + 5e + 4)·(n + 1)^e ≤ (C + 5e + 12)·((n + 1)^e + n + 1)`, and the private
`pairCount_computes` adds `2n + 5`. -/
theorem pairLenCheckTM_computes (C e : ℕ) :
    (pairLenCheckTM C e).ComputesFunInTime
      (fun x => [match pairDecode x with
        | some (a, b) => decide (b.length ≤ C * (a.length + 1) ^ e)
        | none => false])
      (fun n => (C + 5 * e + 17) * ((n + 1) ^ e + n + 1)) := by
  have hlen (x : List Bool) : (((pairDecode x).map Prod.fst).getD []).length ≤ x.length := by
    cases hd : pairDecode x with
    | none => simp
    | some ab =>
      rcases ab with ⟨a, b⟩
      simp only [Option.map_some, Option.getD_some]
      rw [Turing.eq_pairEncode_of_pairDecode x a b hd, length_pairEncode]
      omega
  have hG : (bufferedCompTM (pairExtractTM true false) (polyUnaryTM C e)).ComputesFunInTime
      (fun x => List.replicate
        (C * ((((pairDecode x).map Prod.fst).getD []).length + 1) ^ e) true)
      (fun n => (C + 5 * e + 12) * ((n + 1) ^ e + n + 1)) := by
    intro x
    have hpow := Nat.pow_le_pow_left (Nat.add_le_add_right (hlen x) 1) e
    have h := bufferedCompTM_computesInTime _ _ (pairExtractTM_fst x)
      (polyUnaryTM_computes C e (((pairDecode x).map Prod.fst).getD []))
    refine h.mono ?_
    dsimp only
    have := hlen x
    have h3 := Nat.mul_le_mul_left (C + 5 * e + 4) hpow
    generalize (x.length + 1) ^ e = P at h3 ⊢
    generalize ((((pairDecode x).map Prod.fst).getD []).length + 1) ^ e = P' at h3 ⊢
    have h4 : (C + 5 * e + 12) * (P + x.length + 1) =
        (C + 5 * e + 4) * P + 8 * P + (C + 5 * e + 12) * (x.length + 1) := by ring
    have h5 : 8 * (x.length + 1) ≤ (C + 5 * e + 12) * (x.length + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  intro x
  have h := pairCount_computes hG x
  have hh : (pairLenCheckTM C e).ComputesInTime x
      [match pairDecode x with
        | some (a, b) => decide (b.length ≤ C * (a.length + 1) ^ e)
        | none => false]
      ((C + 5 * e + 12) * ((x.length + 1) ^ e + x.length + 1) + 2 * x.length + 5) := by
    cases hd : pairDecode x with
    | none => simpa [pairLenCheckTM, hd] using h
    | some uv => cases uv; simpa [pairLenCheckTM, hd] using h
  refine hh.mono ?_
  dsimp only
  generalize (x.length + 1) ^ e = P
  have h6 : (C + 5 * e + 17) * (P + x.length + 1) =
      (C + 5 * e + 12) * (P + x.length + 1) + 5 * (P + x.length + 1) := by ring
  omega

/-- **P8, threaded length-bound check** (new; the
original-bound re-check discipline of the Exercise-2.1 reverse verifier,
in threaded form). On `pairEncode a b`, decide `|b| ≤ C·(|a|+1)^e` — the
original input `a` travels with the payload precisely so that this bound
is checked against *it*, the audited rule being that merely fitting inside
the enlarged region does not authorize a witness. Malformed inputs answer
`false`.

**Construction sketch.** Parse the two components onto work tapes (the
extractor scans above); lay down `C·(|a|+1)^e` in unary by the
polynomial-evaluation loop; compare against `|b|` by a parallel countdown;
emit the single verdict bit. -/
theorem computesFunInTime_pairLenCheck (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun x => [match pairDecode x with
          | some (a, b) => decide (b.length ≤ C * (a.length + 1) ^ e)
          | none => false])
        fun n => c * (n + 1) ^ (e + 1) := by
  obtain ⟨F, a, hF⟩ := computesFunInTime_pairFst
  obtain ⟨U, b, hU⟩ := computesFunInTime_polyUnary C e
  obtain ⟨G, d, hG⟩ := computesFunInTime_comp hF hU
    (by
      intro m n h
      exact Nat.mul_le_mul_left b
        (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) (e + 1)))
  refine ⟨pairCountTM G, d * (a + b * (a + 1) ^ (e + 1) + 1) + 7, fun x => ?_⟩
  have hc := pairCount_computes hG x
  have hh : (pairCountTM G).ComputesInTime x
      [match pairDecode x with
        | some (u, v) => decide (v.length ≤ C * (u.length + 1) ^ e)
        | none => false]
      (d * (a * (x.length + 1) + b * (a * (x.length + 1) + 1) ^ (e + 1) + 1) +
        2 * x.length + 5) := by
    cases hd : pairDecode x with
    | none => simpa [hd, Function.comp_apply] using hc
    | some uv => cases uv; simpa [hd, Function.comp_apply] using hc
  apply hh.mono
  let P := (x.length + 1) ^ (e + 1)
  have hp : 1 ≤ P := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hn : x.length + 1 ≤ P := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos x.length)
      (show 1 ≤ e + 1 by omega)
  have hbase : a * (x.length + 1) + 1 ≤ (a + 1) * (x.length + 1) := by
    simp only [Nat.add_mul, Nat.one_mul]; omega
  have hpow : (a * (x.length + 1) + 1) ^ (e + 1) ≤ (a + 1) ^ (e + 1) * P := by
    simpa only [Nat.mul_pow] using Nat.pow_le_pow_left hbase (e + 1)
  have hsum : a * (x.length + 1) + b * (a * (x.length + 1) + 1) ^ (e + 1) + 1 ≤
      (a + b * (a + 1) ^ (e + 1) + 1) * P := by
    calc
      _ ≤ a * P + b * ((a + 1) ^ (e + 1) * P) + P :=
        Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left a hn)
          (Nat.mul_le_mul_left b hpow)) hp
      _ = _ := by ring
  calc
    _ = d * (a * (x.length + 1) + b * (a * (x.length + 1) + 1) ^ (e + 1) + 1) +
        (2 * x.length + 5) := by omega
    _ ≤ d * ((a + b * (a + 1) ^ (e + 1) + 1) * P) + 7 * P :=
      Nat.add_le_add (Nat.mul_le_mul_left d hsum) (by omega)
    _ = (d * (a + b * (a + 1) ^ (e + 1) + 1) + 7) * P := by ring

/-- **The marker strip's time**. On `pairEncode a v` the strip outputs `pairEncode a u` where `u` is
`v` cut at its last `true` (`Turing.splitAtLastTrue`), and `[]` if `v` has no `true` or the input is
malformed, within `150·(n + 1)` steps: linear.

**Proof sketch.** Today's proof of `computesFunInTime_stripLast` before its weakening (and
Catalog's `f2_strip_linear`), with the constants of the named parts: the decider
(`bufferedCompTM_computesFunInTime` over `pairExtractTM_snd` and the private `anyTrue_computes`)
runs within `2·(5(n + 1) + (5(n + 1) + 1) + 1)`, the raw strip within `4(n + 1)`
(`rawStrip_computes`) and the empty constant within `1`, and `timedCondTM_computes` gives
`5·(20(n + 1) + 4 + 4(n + 1) + 1) ≤ 150·(n + 1)`. The output identity is the private
`catalogMarker_cases` with `Turing.eq_pairEncode_of_pairDecode`. -/
theorem stripLastTM_computes :
    stripLastTM.ComputesFunInTime
      (fun x => match pairDecode x with
        | some (a, v) =>
          match splitAtLastTrue v with
          | some u => pairEncode a u
          | none => []
        | none => [])
      (fun n => 150 * (n + 1)) := by
  have hD := bufferedCompTM_computesFunInTime pairExtractTM_snd anyTrue_computes
    (by intro m n h; exact Nat.add_le_add_right h 1)
  have hE : (constTM []).ComputesFunInTime (fun _ => []) (fun _ => 1) :=
    fun x => constTM_computes [] x
  have hM := timedCondTM_computes (p := fun x => ((pairDecode x).map Prod.snd |>.getD []).any id)
    hD rawStrip_computes hE
  intro x
  have hm := hM x
  have hh : stripLastTM.ComputesInTime x
      (match pairDecode x with
        | some (u, v) => match splitAtLastTrue v with
          | some w => pairEncode u w
          | none => []
        | none => [])
      (5 * (2 * (5 * (x.length + 1) + (5 * (x.length + 1) + 1) + 1) +
        max (4 * (x.length + 1)) 1 + 1)) := by
    cases hd : pairDecode x with
    | none => simpa [stripLastTM, hd] using hm
    | some uv =>
      rcases uv with ⟨u, v⟩
      rcases catalogMarker_cases v with ⟨ha, hs⟩ | ⟨w, ha, hs, hp⟩
      · simpa [stripLastTM, hd, ha, hs] using hm
      · have hx : splitAtLastTrue x = some (pairEncode u w) := by
          rw [Turing.eq_pairEncode_of_pairDecode x u v hd]
          exact hp _
        simpa [stripLastTM, hd, ha, hs, hx] using hm
  refine hh.mono ?_
  dsimp only
  have : max (4 * (x.length + 1)) 1 = 4 * (x.length + 1) := max_eq_left (by omega)
  omega

/-- **P9, marker strip** (harvest: the semantic layer
is the Exercise-2.1 batch's proved `stripCertificate` family; the machine
is new). On `pairEncode a v`, strip `v` at its **last** `true`
(`Turing.splitAtLastTrue`) and re-emit the threaded pair with the stripped
witness; an all-`false` region or a malformed input yields `[]` (the
rejection the downstream guard reads).

**Construction sketch.** Parse `a` and `v` onto work tapes; locate the
last `true` of `v` by one reverse sweep; then — and only then — emit the
re-encoded pair (doubled `a`, separator, the prefix of `v` before that
marker). All-`false` regions and parse failures halt with nothing
emitted. -/
theorem computesFunInTime_stripLast :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun x => match pairDecode x with
          | some (a, v) =>
            match splitAtLastTrue v with
            | some u => pairEncode a u
            | none => []
          | none => [])
        fun n => c * (n + 1) ^ 2 := by
  obtain ⟨S, a, hS⟩ := computesFunInTime_pairSnd
  obtain ⟨D, b, hD⟩ := computesFunInTime_comp hS anyTrue_computes
    (by intro m n h; exact Nat.add_le_add_right h 1)
  have hD' : D.ComputesFunInTime
      (fun x => [((pairDecode x).map Prod.snd |>.getD []).any id])
      (fun n => b * (a * (n + 1) + (a * (n + 1) + 1) + 1)) := by
    simpa only [Function.comp_apply] using hD
  obtain ⟨E, c, hE⟩ := computesFunInTime_const ([] : List Bool)
  obtain ⟨M, d, hM⟩ := computesFunInTime_cond hD' rawStrip_computes hE
  refine ⟨M, d * (2 * b * (a + 1) + (4 + c) + 1), fun x => ?_⟩
  have hh : M.ComputesInTime x
      (match pairDecode x with
        | some (u, v) => match splitAtLastTrue v with
          | some w => pairEncode u w
          | none => []
        | none => [])
      (d * (b * (a * (x.length + 1) + (a * (x.length + 1) + 1) + 1) +
        max (4 * (x.length + 1)) (c * (x.length + 1)) + 1)) := by
    have hm := hM x
    cases hd : pairDecode x with
    | none => simpa [hd] using hm
    | some uv =>
      rcases uv with ⟨u, v⟩
      rcases catalogMarker_cases v with ⟨ha, hs⟩ | ⟨w, ha, hs, hp⟩
      · simpa [hd, ha, hs] using hm
      · have hx : splitAtLastTrue x = some (pairEncode u w) := by
          rw [Turing.eq_pairEncode_of_pairDecode x u v hd]
          exact hp _
        simpa [hd, ha, hs, hx] using hm
  apply hh.mono
  have hbase : a * (x.length + 1) + 1 ≤ (a + 1) * (x.length + 1) := by
    simp only [Nat.add_mul, Nat.one_mul]; omega
  have hg : b * (a * (x.length + 1) + (a * (x.length + 1) + 1) + 1) ≤
      (2 * b * (a + 1)) * (x.length + 1) := by
    calc
      _ = (2 * b) * (a * (x.length + 1) + 1) := by ring
      _ ≤ (2 * b) * ((a + 1) * (x.length + 1)) := Nat.mul_le_mul_left _ hbase
      _ = _ := by ring
  have hm : max (4 * (x.length + 1)) (c * (x.length + 1)) ≤
      (4 + c) * (x.length + 1) := by
    apply max_le
    · exact Nat.mul_le_mul_right _ (by omega)
    · exact Nat.mul_le_mul_right _ (by omega)
  have hb : b * (a * (x.length + 1) + (a * (x.length + 1) + 1) + 1) +
      max (4 * (x.length + 1)) (c * (x.length + 1)) + 1 ≤
      (2 * b * (a + 1) + (4 + c) + 1) * (x.length + 1) := by
    calc
      _ ≤ (2 * b * (a + 1)) * (x.length + 1) +
          (4 + c) * (x.length + 1) + (x.length + 1) :=
        Nat.add_le_add (Nat.add_le_add hg hm) (by omega)
      _ = _ := by ring
  have hn : x.length + 1 ≤ (x.length + 1) ^ 2 := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos x.length)
      (show 1 ≤ 2 by omega)
  calc
    _ ≤ d * ((2 * b * (a + 1) + (4 + c) + 1) * (x.length + 1)) := Nat.mul_le_mul_left d hb
    _ ≤ d * ((2 * b * (a + 1) + (4 + c) + 1) * (x.length + 1) ^ 2) :=
      Nat.mul_le_mul_left d (Nat.mul_le_mul_left _ hn)
    _ = _ := by ring

/-- The audited split-search step preserves every existing candidate bit;
at the one-past-end state it stalls. -/
private def splitStep (w s : List Bool) : List Bool :=
  if s.length ≤ w.length then s ++ [true] else s

/-- Split-search acceptance is the exact padding length equation. -/
private def splitAccept (C e : ℕ) (w s : List Bool) : Bool :=
  decide (s.length + C * (s.length + 1) ^ e = w.length)

/-- The length invariant is closed even on arbitrary candidate bit patterns. -/
private lemma splitStep_inv (w s : List Bool) (hs : s.length ≤ w.length + 1) :
    (splitStep w s).length ≤ w.length + 1 := by
  unfold splitStep
  split <;> simp_all <;> omega

/-- All orbit points tested by the loop are precisely the unary candidates.
**Proof sketch.** Before fuel is exhausted the current length is the iteration
index, so the step appends one true. The extra one-past-end state is included. -/
private lemma splitStep_orbit (w : List Bool) : ∀ i, i ≤ w.length + 1 →
    (splitStep w)^[i] [] = List.replicate i true := by
  intro i
  induction i with
  | zero => intro hi; rfl
  | succ i ih =>
    intro hi
    rw [Function.iterate_succ_apply', ih (by omega)]
    simp only [splitStep, List.length_replicate, if_pos (by omega : i ≤ w.length)]
    exact (List.replicate_succ').symm

/-- Extensional equality of search predicates on the searched list preserves
both the least-success index and failure. -/
private lemma catalogFind_congr {α : Type} (xs : List α) (p q : α → Bool)
    (h : ∀ a ∈ xs, p a = q a) : xs.find? p = xs.find? q := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.find?_cons, h a (by simp)]
    rw [ih (fun b hb => h b (by simp [hb]))]

/-- The orbit predicate and `solveSplit` use the same finite search, including
its unsuccessful branch. The Boolean equality is converted explicitly. -/
private lemma splitFind_eq (C e : ℕ) (w : List Bool) :
    (List.range (w.length + 1)).find?
      (fun i => splitAccept C e w ((splitStep w)^[i] [])) = solveSplit C e w.length := by
  apply catalogFind_congr
  intro i hi
  have hi' : i ≤ w.length := by simpa only [List.mem_range, Nat.lt_succ_iff] using hi
  rw [splitStep_orbit w i (by omega)]
  apply Bool.eq_iff_iff.mpr
  simp only [splitAccept, List.length_replicate, decide_eq_true_eq, beq_iff_eq]

/-- Each successful orbit payload is exactly the split at the returned index;
exhaustion returns the same empty word on both sides. -/
private lemma splitLoop_result (C e : ℕ) (w : List Bool) :
    (match (List.range (w.length + 1)).find?
        (fun i => splitAccept C e w ((splitStep w)^[i] [])) with
      | some i => pairEncode (w.take ((splitStep w)^[i] []).length)
          (w.drop ((splitStep w)^[i] []).length)
      | none => []) =
    (match solveSplit C e w.length with
      | some i => pairEncode (w.take i) (w.drop i)
      | none => []) := by
  rw [splitFind_eq]
  cases hs : solveSplit C e w.length with
  | none => rfl
  | some i =>
    have hi := List.mem_of_find?_eq_some hs
    have hi' : i ≤ w.length := by simpa only [List.mem_range, Nat.lt_succ_iff] using hi
    simp only [splitStep_orbit w i (by omega), List.length_replicate]

/-- The loop overhead raises the body's polynomial exponent by exactly one.
**Proof sketch.** Bound the additive one by `(n+1)^(e+1)` and the factor `n+2`
by `2(n+1)`, then combine powers. This includes `n=0` and `e=0`. -/
private lemma splitLoop_bound (c A e n : ℕ) :
    c * (A * (n + 1) ^ (e + 1) + 1) * (n + 2) ≤
      (2 * c * (A + 1)) * (n + 1) ^ (e + 2) := by
  have hp : 1 ≤ (n + 1) ^ (e + 1) := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hfirst : A * (n + 1) ^ (e + 1) + 1 ≤ (A + 1) * (n + 1) ^ (e + 1) := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  calc
    _ ≤ c * ((A + 1) * (n + 1) ^ (e + 1)) * (2 * (n + 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left c hfirst) (by omega)
    _ = _ := by rw [show e + 2 = (e + 1) + 1 by omega, Nat.pow_succ]; ring

/-- A physical input position after consuming a unary count, saturated at the
right boundary. -/
private def splitPos (w : List Bool) (j : ℕ) : Fin (w.length + 2) :=
  ⟨min j w.length + 1, by omega⟩

/-- A saturated countdown read is blank exactly after all input bits. -/
private lemma splitPos_read {k : ℕ} {S : Type} (w : List Bool)
    (cfg : Cfg k Bool S w) (j : ℕ) (hp : cfg.inputPos = splitPos w j) :
    cfg.inputSymbol = if h : j < w.length then some (w[j]'h) else none := by
  by_cases hj : j < w.length
  · rw [dif_pos hj]
    exact inputSymbolInner j
      (by simp [hp, splitPos, Nat.min_eq_left (by omega : j ≤ w.length), Nat.add_comm]) hj
  · rw [dif_neg hj]
    simp [Cfg.inputSymbol, hp, splitPos, Nat.min_eq_right (by omega : w.length ≤ j)]

/-- A forward move increments a saturated unary countdown position. -/
private lemma splitPos_succ (w : List Bool) (j : ℕ) :
    moveInputPos (splitPos w j) .pos = splitPos w (j + 1) := by
  by_cases hj : j < w.length
  · rw [moveInputPos_pos_of_ne_right _ (by simp [splitPos] <;> omega)]
    apply Fin.ext
    simp only [splitPos, Fin.val_mk]
    omega
  · have he : splitPos w j = ⟨w.length + 1, by omega⟩ := by
      apply Fin.ext
      simp [splitPos, Nat.min_eq_right (by omega : w.length ≤ j)]
    rw [he, SignType.pos_eq_one, moveInputPos_rightBoundary]
    apply Fin.ext
    simp [splitPos, Nat.min_eq_right (by omega : w.length ≤ j + 1)]

/-- A partially cleared unary scratch word, with its remaining suffix exposed. -/
private def splitScratch (q j : ℕ) (z : ℤ) : Option Bool :=
  if (j : ℤ) ≤ z ∧ z < q then some true else none

/-- Clearing the exposed scratch cell advances the cleared prefix by one. -/
private lemma splitScratch_erase (q j : ℕ) :
    Function.update (splitScratch q j) (j : ℤ) none = splitScratch q (j + 1) := by
  funext z
  by_cases hz : z = (j : ℤ)
  · subst z; simp [splitScratch]
  · rw [Function.update_of_ne hz]
    have he : ((j : ℤ) ≤ z ∧ z < q) ↔ (((j + 1 : ℕ) : ℤ) ≤ z ∧ z < q) := by omega
    simp only [splitScratch, he]

/-- The rejection cleanup preserves all candidate bits, appends only within
the input-length range, clears every unary scratch tape, and restores heads.
State 4 is an absorbing return seam, suitable for a first-return embedding. -/
private def splitRestoreTM (k : ℕ) : FinTM Bool where
  k := k + 1
  State := Fin 5 × Bool
  tm := {
    q₀ := (0, false)
    tr := fun q inp work => match q.1.val with
      | 0 => match work 0 with
        | some _ => ⟨.pos, Fin.cases (none, .pos) (fun _ => (some none, .pos)),
            none, some (0, q.2 || inp.isNone)⟩
        | none => ⟨0, Fin.cases (if q.2 then (none, .neg) else (some (some true), .neg))
            (fun _ => (some none, .neg)), none, some (1, false)⟩
      | 1 => match work 0 with
        | some _ => ⟨0, fun _ => (none, .neg), none, some (1, false)⟩
        | none => ⟨0, fun _ => (none, .pos), none, some (2, false)⟩
      | 2 => controlAction .neg (some (3, false))
      | 3 => match inp with
        | some _ => controlAction .neg (some (3, false))
        | none => controlAction .pos (some (4, false))
      | _ => controlAction 0 (some (4, false)) }

/-- The clearing scan has consumed `j` candidate cells and erased exactly that
prefix on each scratch tape; the physical input tracks the same count. -/
private def splitRestoreScan (k : ℕ) (w s : List Bool) (j : ℕ) :
    Cfg (k + 1) Bool (splitRestoreTM k).State w :=
  ⟨some (0, decide (w.length < j)), splitPos w j,
    Fin.cases (bufferTape s) (fun _ => splitScratch (s.length + 1) j), fun _ => j, []⟩

/-- The silent cleanup scans each candidate bit once, including false bits.
**Proof sketch.** Each transition preserves tape 0, clears one cell on every
scratch tape, and advances all heads. The overflow flag records precisely
whether more candidate cells than native input cells have been consumed. -/
private lemma splitRestore_scan (k : ℕ) (w s : List Bool) : ∀ j, j ≤ s.length →
    (splitRestoreTM k).tm.runFrom (splitRestoreScan k w s 0) j =
      splitRestoreScan k w s j := by
  intro j
  induction j with
  | zero => intro hj; rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hw : (splitRestoreScan k w s j).workTapeSymbols 0 = some (s[j]'(by omega)) := by
      simp [splitRestoreScan, Cfg.workTapeSymbols,
        List.getElem?_eq_getElem (by omega : j < s.length)]
    have hin := splitPos_read w (splitRestoreScan k w s j) j rfl
    unfold MultiTapeTM.step
    change ((splitRestoreTM k).tm.tr (0, decide (w.length < j)) _ _).apply _ = _
    simp only [splitRestoreTM, hw]
    refine Cfg.ext ?_ (splitPos_succ w j) ?_ ?_ rfl
    · change some (0, decide (w.length < j) ||
        (splitRestoreScan k w s j).inputSymbol.isNone) = some (0, decide (w.length < j + 1))
      rw [hin]
      by_cases hjn : j < w.length
      · simp [hjn, show ¬w.length < j by omega, show ¬w.length < j + 1 by omega]
      · simp [hjn, show w.length < j + 1 by omega]
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · exact splitScratch_erase _ _
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [Action.apply, splitRestoreScan]

/-- A cleaned configuration has only the candidate on tape zero; all work
heads are synchronized and the physical output is empty. -/
private def splitRestoreClean (k : ℕ) (w s : List Bool)
    (q : (splitRestoreTM k).State) (p : Fin (w.length + 2)) (h : ℤ) :
    Cfg (k + 1) Bool (splitRestoreTM k).State w :=
  ⟨some q, p, Fin.cases (bufferTape s) (fun _ => fun _ => none), fun _ => h, []⟩

/-- The end-of-scan step clears the final extra scratch cell and appends to
tape 0 exactly when the old candidate length is at most the input length. -/
private lemma splitRestore_append (k : ℕ) (w s : List Bool) :
    (splitRestoreTM k).tm.step (splitRestoreScan k w s s.length) =
      splitRestoreClean k w (splitStep w s) (1, false)
        (splitPos w s.length) (s.length - 1) := by
  have hw : (splitRestoreScan k w s s.length).workTapeSymbols 0 = none := by
    simp [splitRestoreScan, Cfg.workTapeSymbols]
  unfold MultiTapeTM.step
  change ((splitRestoreTM k).tm.tr (0, decide (w.length < s.length)) _ _).apply _ = _
  simp only [splitRestoreTM, hw]
  by_cases hs : s.length ≤ w.length
  · have hflag : decide (w.length < s.length) = false := by simp; omega
    rw [hflag]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa [Action.apply, splitRestoreClean, splitStep, hs] using (bufferTape_append s true).symm
      · change Function.update (splitScratch (s.length + 1) s.length) (s.length : ℤ) none = _
        rw [splitScratch_erase]
        funext z
        simp [splitRestoreClean, splitScratch]
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [Action.apply, splitRestoreScan, splitRestoreClean, sub_eq_add_neg]
  · have hflag : decide (w.length < s.length) = true := by simp; omega
    rw [hflag]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [Action.apply, splitRestoreScan, splitRestoreClean, splitStep, hs]
      · change Function.update (splitScratch (s.length + 1) s.length) (s.length : ℤ) none = _
        rw [splitScratch_erase]
        funext z
        simp [splitRestoreClean, splitScratch]
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [Action.apply, splitRestoreScan, splitRestoreClean, sub_eq_add_neg]

/-- Candidate-guided rewind restores every head, including heads on tapes
that have already been cleared. No candidate bit is altered. -/
private lemma splitRestore_rewind (k : ℕ) (w s : List Bool) (p : Fin (w.length + 2)) :
    ∀ j, j ≤ s.length →
      (splitRestoreTM k).tm.runFrom
        (splitRestoreClean k w s (1, false) p ((j : ℤ) - 1)) (j + 1) =
        splitRestoreClean k w s (2, false) p 0 := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [MultiTapeTM.step, splitRestoreClean, splitRestoreTM, Cfg.workTapeSymbols,
      Fin.cases_zero, Nat.cast_zero, zero_sub, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply, splitRestoreScan]
  | succ j ih =>
    intro hj
    have hs : (splitRestoreTM k).tm.step
        (splitRestoreClean k w s (1, false) p (((j + 1 : ℕ) : ℤ) - 1)) =
        splitRestoreClean k w s (1, false) p ((j : ℤ) - 1) := by
      have he : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [he]
      simp only [MultiTapeTM.step, splitRestoreClean, splitRestoreTM, Cfg.workTapeSymbols,
        Fin.cases_zero, bufferTape_nat, List.getElem?_eq_getElem (by omega : j < s.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Complete rejection cleanup restores exactly the audited state-word seam.
It works for arbitrary candidate bits, and its one-past-end stall is silent.
**Proof sketch.** Scan and erase `|s|` cells, handle the final scratch cell,
rewind synchronized heads along the preserved candidate, then rewind input.
The cost is at most `2|s|+|w|+5`, and every transition is silent. -/
private lemma splitRestore_run (k : ℕ) (w s : List Bool) :
    ∃ t ≤ 2 * s.length + w.length + 5,
      (splitRestoreTM k).tm.runFrom (splitRestoreScan k w s 0) t =
        Cfg.ofWords (4, false) (stateWord (k + 1) (splitStep w s)) := by
  have hlen : s.length ≤ (splitStep w s).length := by
    unfold splitStep
    split <;> simp
  obtain ⟨r, hr, he⟩ := catalogRewind (splitRestoreTM k).tm (2, false) (3, false)
    (some (4, false)) (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl)
    (splitRestoreClean k w (splitStep w s) (2, false) (splitPos w s.length) 0) rfl
  have hp : (splitPos w s.length).val ≤ w.length + 1 := by simp [splitPos] <;> omega
  have hfirst : (splitRestoreTM k).tm.runFrom (splitRestoreScan k w s 0) (s.length + 1) =
      splitRestoreClean k w (splitStep w s) (1, false) (splitPos w s.length) (s.length - 1) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', splitRestore_scan k w s _ (le_refl _),
      splitRestore_append]
  refine ⟨(s.length + 1) + (s.length + 1) + r, ?_, ?_⟩
  · change r ≤ (splitPos w s.length).val + 2 at hr
    omega
  · rw [MultiTapeTM.runFrom_add _ _ r,
      MultiTapeTM.runFrom_add _ (s.length + 1) (s.length + 1),
      hfirst, splitRestore_rewind k w (splitStep w s) _ _ hlen, he]
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;>
        simp [splitRestoreClean, Cfg.ofWords, stateWord]
    · rfl
    · rfl

/-- Replace source emissions by native-input consumption. Tape zero retains
the candidate; the source bank occupies successor-indexed tapes. A finite
flag remembers consumption past the native right boundary. -/
private def splitCountAction {k : ℕ} {S H : Type} (emb : S → Bool → H) (ret : Bool → H)
    (over : Bool) (inp : Option Bool) (a : Action k Bool S) : Action (k + 1) Bool H :=
  let over' := over || (a.output.isSome && inp.isNone)
  ⟨if a.output.isSome then .pos else 0, Fin.cases (none, 0) a.workTapes, none,
    some (match a.state with | some q => emb q over' | none => ret over')⟩

/-- Source configurations use an empty virtual input and arbitrary initialized
work tapes. Their output length is consumed after the candidate's length. -/
private def splitCountCfg {k : ℕ} {S H : Type} (emb : S → Bool → H) (ret : Bool → H)
    (w s : List Bool) (c : Cfg k Bool S []) : Cfg (k + 1) Bool H w :=
  let over := decide (w.length < s.length + c.output.length)
  ⟨some (match c.state with | some q => emb q over | none => ret over),
    splitPos w (s.length + c.output.length), Fin.cases (bufferTape s) c.workTapes,
    Fin.cases 0 c.workTapePos, []⟩

/-- Consuming one additional symbol updates the saturation flag exactly. -/
private lemma splitCount_over {k : ℕ} {S : Type} (w : List Bool)
    (cfg : Cfg k Bool S w) (j : ℕ) (hp : cfg.inputPos = splitPos w j) :
    (decide (w.length < j) || cfg.inputSymbol.isNone) = decide (w.length < j + 1) := by
  rw [splitPos_read w cfg j hp]
  by_cases hj : j < w.length
  · simp [hj, show ¬w.length < j by omega, show ¬w.length < j + 1 by omega]
  · simp [hj, show w.length < j + 1 by omega]

/-- One transformed step consumes exactly its optional source emission,
preserves the candidate, and reproduces all source-bank writes and moves.
**Proof sketch.** Split on the optional output and on tape zero versus source
tapes. The one-emission case is precisely the saturated-position increment
and overflow update; the zero-emission case leaves both unchanged. -/
private lemma splitCount_apply {k : ℕ} {S H : Type} (emb : S → Bool → H) (ret : Bool → H)
    (w s : List Bool) (c : Cfg k Bool S []) (a : Action k Bool S) :
    (splitCountAction emb ret (decide (w.length < s.length + c.output.length))
      (splitCountCfg emb ret w s c).inputSymbol a).apply (splitCountCfg emb ret w s c) =
      splitCountCfg emb ret w s (a.apply c) := by
  have hflag := splitCount_over w (splitCountCfg emb ret w s c)
    (s.length + c.output.length) rfl
  cases ho : a.output with
  | none =>
    refine Cfg.ext ?_ ?_ ?_ ?_ rfl
    · simp [splitCountAction, splitCountCfg, Action.apply, ho]
    · simpa [splitCountAction, splitCountCfg, Action.apply, ho] using
        moveInputPos_zero (splitPos w (s.length + c.output.length))
    · funext i; refine Fin.cases ?_ (fun i => ?_) i <;> rfl
    · funext i; refine Fin.cases ?_ (fun i => ?_) i <;>
        simp [splitCountAction, splitCountCfg, Action.apply]
  | some b =>
    refine Cfg.ext ?_ ?_ ?_ ?_ rfl
    · simpa [splitCountAction, splitCountCfg, Action.apply, ho, Nat.add_assoc] using
        congrArg (fun flag => some (match a.state with | some q => emb q flag | none => ret flag)) hflag
    · simpa [splitCountAction, splitCountCfg, Action.apply, ho, Nat.add_assoc] using
        splitPos_succ w (s.length + c.output.length)
    · funext i; refine Fin.cases ?_ (fun i => ?_) i <;> rfl
    · funext i; refine Fin.cases ?_ (fun i => ?_) i <;>
        simp [splitCountAction, splitCountCfg, Action.apply]

/-- A counted source run follows the original work-bank computation exactly,
including a final emitting halt, while consuming its output on native input.
**Proof sketch.** Empty virtual input always reads blank. Apply the one-step
correspondence through the source's first halt, as in `capture_run`; the
physical output stays empty throughout. -/
private lemma splitCount_run {k : ℕ} {S H : Type}
    (tm : MultiTapeTM k Bool S) (host : MultiTapeTM (k + 1) Bool H)
    (emb : S → Bool → H) (ret : Bool → H)
    (hagree : ∀ q over inp work, host.tr (emb q over) inp work =
      splitCountAction emb ret over inp (tm.tr q none (fun i => work i.succ)))
    (w s : List Bool) (c : Cfg k Bool S []) (t : ℕ)
    (hlive : ∀ j < t, ¬(tm.runFrom c j).Halted) :
    host.runFrom (splitCountCfg emb ret w s c) t =
      splitCountCfg emb ret w s (tm.runFrom c t) := by
  have hstep (d : Cfg k Bool S []) (hs : ¬d.Halted) :
      host.step (splitCountCfg emb ret w s d) = splitCountCfg emb ret w s (tm.step d) := by
    cases hq : d.state with
    | none => exact False.elim (hs hq)
    | some q =>
      have hstate : (splitCountCfg emb ret w s d).state =
          some (emb q (decide (w.length < s.length + d.output.length))) := by
        simp [splitCountCfg, hq]
      have hsource : d.inputSymbol = none := by
        unfold Cfg.inputSymbol
        split_ifs with h₀ h₁
        · rfl
        · rfl
        · have hp := d.inputPos.isLt
          simp only [Fin.ext_iff, Fin.val_zero] at h₀
          simp only [List.length_nil] at hp
          simp only [List.length_nil, Nat.zero_add, Nat.cast_one, Fin.ext_iff, Fin.val_one] at h₁
          omega
      have hwork : (fun i => (splitCountCfg emb ret w s d).workTapeSymbols i.succ) =
          d.workTapeSymbols := by
        funext i; simp [splitCountCfg, Cfg.workTapeSymbols]
      simp only [MultiTapeTM.step, hstate, hq]
      rw [hagree, hwork, hsource]
      exact splitCount_apply emb ret w s d _
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun j hj => hlive j (by omega)),
      hstep _ (hlive t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

/-- The in-file generator's loop phase ends with every unary scratch head
back at zero, ready for the restoration controller. The source input is empty;
its loop side length is supplied by the initialized work tapes.
**Proof sketch.** Run the existing exact nested-loop invariant over the full
box and then take the final halting transition. No fresh generator proof is
assumed, and the zero coefficient is included. -/
private lemma splitPoly_loop_end (c C q : ℕ) (hq : 0 < q) :
    (catalogPolyUnaryTM c C).tm.runFrom
      (catalogPolyCfg (C := C) [] q (.loop (Fin.last c)) (fun _ => 0) [])
      (catalogPolyCost q C (c + 1) + 1) =
      {catalogPolyCfg (C := C) [] q (.advance (Fin.last (c + 1))) (fun _ => 0)
        (List.replicate (C * q ^ (c + 1)) true) with state := none} := by
  have hl := catalogPoly_loop (c := c) (C := C) [] q hq c (by omega)
    (fun _ => 0) (by simp) [] q 0 (by omega)
  have hout : q * (C * q ^ c) = C * q ^ (c + 1) := by rw [Nat.pow_succ]; ring
  have hloop : (catalogPolyUnaryTM c C).tm.runFrom
      (catalogPolyCfg (C := C) [] q (.loop (Fin.last c)) (fun _ => 0) [])
      (catalogPolyCost q C (c + 1)) =
      catalogPolyCfg (C := C) [] q (.advance (Fin.last (c + 1))) (fun _ => 0)
        (List.replicate (C * q ^ (c + 1)) true) := by
    simpa [catalogPolyCost, hout] using hl
  rw [MultiTapeTM.runFrom_succ_eq_step', hloop]
  simp only [MultiTapeTM.step, catalogPolyCfg, catalogPolyUnaryTM, Fin.val_last,
    Nat.lt_irrefl, ↓reduceDIte]
  refine Cfg.ext rfl ?_ rfl ?_ ?_
  · rfl
  · funext i; simp [MultiTapeTM.step, catalogPolyUnaryTM, Action.apply, catalogPolyCfg]
  · simp [MultiTapeTM.step, catalogPolyUnaryTM, Action.apply, catalogPolyCfg]

/-- A run reaching an absorbing control state has a least such entry, and its
configuration at that first entry is already the final configuration.
**Proof sketch.** Choose the least hit. Absorption makes its entire suffix
constant, so the bounded endpoint identifies the first-hit configuration. -/
private lemma catalogFirstEntry {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (q : S) (c d : Cfg k Bool S w) (T : ℕ)
    (hfix : ∀ z : Cfg k Bool S w, z.state = some q → tm.step z = z)
    (hd : d.state = some q) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, (∀ j < t, (tm.runFrom c j).state ≠ some q) ∧ tm.runFrom c t = d := by
  classical
  have hh : ∃ t, (tm.runFrom c t).state = some q := ⟨T, by rw [hT, hd]⟩
  let t := Nat.find hh
  have ht : t ≤ T := Nat.find_min' hh (by rw [hT, hd])
  have hs : (tm.runFrom c t).state = some q := Nat.find_spec hh
  refine ⟨t, ht, fun j hj => Nat.find_min hh hj, ?_⟩
  have hconst : tm.runFrom (tm.runFrom c t) (T - t) = tm.runFrom c t :=
    Function.iterate_fixed (hfix _ hs) _
  have he := tm.runFrom_add c t (T - t)
  rw [Nat.add_sub_of_le ht, hT, hconst] at he
  exact he.symm

/-- The cleanup's return seam is absorbing, so its exact restoration can be
exported with positive duration and no earlier return-state visit. -/
private lemma splitRestore_first (k : ℕ) (w s : List Bool) :
    ∃ t, 0 < t ∧ t ≤ 2 * s.length + w.length + 5 ∧
      (∀ j < t, ((splitRestoreTM k).tm.runFrom (splitRestoreScan k w s 0) j).state
        ≠ some (4, false)) ∧
      (splitRestoreTM k).tm.runFrom (splitRestoreScan k w s 0) t =
        Cfg.ofWords (4, false) (stateWord (k + 1) (splitStep w s)) := by
  obtain ⟨T, hTle, hT⟩ := splitRestore_run k w s
  have hfix (z : Cfg (k + 1) Bool (splitRestoreTM k).State w)
      (hz : z.state = some (4, false)) : (splitRestoreTM k).tm.step z = z := by
    unfold MultiTapeTM.step
    rw [hz]
    change (controlAction 0 (some (4, false))).apply z = z
    rw [controlAction_apply, moveInputPos_zero]
    cases z
    simp_all
  obtain ⟨t, ht, hi, he⟩ := catalogFirstEntry (splitRestoreTM k).tm (4, false)
    (splitRestoreScan k w s 0) _ T hfix rfl hT
  refine ⟨t, ?_, ht.trans hTle, hi, he⟩
  by_contra h
  have ht0 : t = 0 := by omega
  have hstate := congrArg Cfg.state he
  simp only [ht0, MultiTapeTM.runFrom_zero, splitRestoreScan, Cfg.ofWords,
    Option.some.injEq, Prod.mk.injEq] at hstate
  have hf := congrArg (fun q : (splitRestoreTM k).State => q.1.val) hstate
  norm_num at hf

/-- Native countdown acceptance is exactly equality of the consumed length
and the original input length; overflow and short counts both reject. -/
private lemma splitCount_accept {k : ℕ} {S H : Type} (emb : S → Bool → H) (ret : Bool → H)
    (w s : List Bool) (c : Cfg k Bool S []) :
    (!decide (w.length < s.length + c.output.length) &&
      (splitCountCfg emb ret w s c).inputSymbol.isNone) =
        decide (s.length + c.output.length = w.length) := by
  rw [splitPos_read w (splitCountCfg emb ret w s c) (s.length + c.output.length) rfl]
  by_cases hlt : s.length + c.output.length < w.length
  · simp [hlt, show ¬s.length + c.output.length = w.length by omega]
  · by_cases he : s.length + c.output.length = w.length
    · simp [he]
    · simp [hlt, he, show w.length < s.length + c.output.length by omega]

/-- Prepare the polynomial loop bank by copying the candidate's length to all
scratch tapes in parallel, adding the extra side-length cell, and rewinding
all work heads along the untouched candidate. State 2 is the return seam. -/
private def splitPrepareTM (k : ℕ) : FinTM Bool where
  k := k + 1
  State := Fin 3 × Bool
  tm := {
    q₀ := (0, false)
    tr := fun q inp work => match q.1.val with
      | 0 => match work 0 with
        | some _ => ⟨.pos, Fin.cases (none, .pos) (fun _ => (some (some true), .pos)),
            none, some (0, q.2 || inp.isNone)⟩
        | none => ⟨0, Fin.cases (none, .neg) (fun _ => (some (some true), .neg)),
            none, some (1, q.2)⟩
      | 1 => match work 0 with
        | some _ => ⟨0, fun _ => (none, .neg), none, some (1, q.2)⟩
        | none => ⟨0, fun _ => (none, .pos), none, some (2, q.2)⟩
      | _ => controlAction 0 (some (2, q.2)) }

/-- During preparation, every scratch tape contains the length scanned so far. -/
private def splitPrepareScan (k : ℕ) (w s : List Bool) (j : ℕ) :
    Cfg (k + 1) Bool (splitPrepareTM k).State w :=
  ⟨some (0, decide (w.length < j)), splitPos w j,
    Fin.cases (bufferTape s) (fun _ => catalogPolyTape j), fun _ => j, []⟩

/-- Preparation copies a unary side length without reading or changing any
candidate bit value. The same induction covers a candidate past native EOF. -/
private lemma splitPrepare_scan (k : ℕ) (w s : List Bool) : ∀ j, j ≤ s.length →
    (splitPrepareTM k).tm.runFrom (splitPrepareScan k w s 0) j =
      splitPrepareScan k w s j := by
  intro j
  induction j with
  | zero => intro hj; rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hw : (splitPrepareScan k w s j).workTapeSymbols 0 = some (s[j]'(by omega)) := by
      simp [splitPrepareScan, Cfg.workTapeSymbols,
        List.getElem?_eq_getElem (by omega : j < s.length)]
    unfold MultiTapeTM.step
    change ((splitPrepareTM k).tm.tr (0, decide (w.length < j)) _ _).apply _ = _
    simp only [splitPrepareTM, hw]
    refine Cfg.ext ?_ (splitPos_succ w j) ?_ ?_ rfl
    · exact congrArg (fun over => some (0, over))
        (splitCount_over w (splitPrepareScan k w s j) j rfl)
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · exact catalogPolyTape_write j
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [Action.apply, splitPrepareScan]

/-- Prepared scratch tapes have side length `|s|+1`, with synchronized heads;
the overflow flag records the candidate's length alone. -/
private def splitPrepareReady (k : ℕ) (w s : List Bool)
    (q : Fin 3) (h : ℤ) : Cfg (k + 1) Bool (splitPrepareTM k).State w :=
  ⟨some (q, decide (w.length < s.length)), splitPos w s.length,
    Fin.cases (bufferTape s) (fun _ => catalogPolyTape (s.length + 1)), fun _ => h, []⟩

/-- Adding the extra side-length cell handles the empty candidate uniformly. -/
private lemma splitPrepare_extra (k : ℕ) (w s : List Bool) :
    (splitPrepareTM k).tm.step (splitPrepareScan k w s s.length) =
      splitPrepareReady k w s 1 (s.length - 1) := by
  have hw : (splitPrepareScan k w s s.length).workTapeSymbols 0 = none := by
    simp [splitPrepareScan, Cfg.workTapeSymbols]
  unfold MultiTapeTM.step
  change ((splitPrepareTM k).tm.tr (0, decide (w.length < s.length)) _ _).apply _ = _
  simp only [splitPrepareTM, hw]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · exact catalogPolyTape_write s.length
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i <;>
      simp [Action.apply, splitPrepareScan, splitPrepareReady, sub_eq_add_neg]

/-- Rewind the synchronized bank along the preserved candidate; each scratch
tape retains its extra cell even though the rewind uses the candidate length. -/
private lemma splitPrepare_rewind (k : ℕ) (w s : List Bool) : ∀ j, j ≤ s.length →
    (splitPrepareTM k).tm.runFrom (splitPrepareReady k w s 1 ((j : ℤ) - 1)) (j + 1) =
      splitPrepareReady k w s 2 0 := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [MultiTapeTM.step, splitPrepareReady, splitPrepareTM, Cfg.workTapeSymbols,
      Fin.cases_zero, Nat.cast_zero, zero_sub, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply]
  | succ j ih =>
    intro hj
    have hs : (splitPrepareTM k).tm.step (splitPrepareReady k w s 1 (((j + 1 : ℕ) : ℤ) - 1)) =
        splitPrepareReady k w s 1 ((j : ℤ) - 1) := by
      have he : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [he]
      simp only [MultiTapeTM.step, splitPrepareReady, splitPrepareTM, Cfg.workTapeSymbols,
        Fin.cases_zero, bufferTape_nat, List.getElem?_eq_getElem (by omega : j < s.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- From the audited state-word seam, preparation takes exactly `2(|s|+1)`
silent steps and initializes every loop head at zero. -/
private lemma splitPrepare_run (k : ℕ) (w s : List Bool) :
    (splitPrepareTM k).tm.runFrom
      (Cfg.ofWords (input := w) (0, false) (stateWord (k + 1) s)) (2 * (s.length + 1)) =
      splitPrepareReady k w s 2 0 := by
  have hinit : Cfg.ofWords (input := w) (0, false) (stateWord (k + 1) s) =
      splitPrepareScan k w s 0 := by
    refine Cfg.ext (by simp [splitPrepareScan, Cfg.ofWords]) ?_ ?_ rfl rfl
    · simp [splitPrepareScan, Cfg.ofWords, splitPos]
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;>
        simp [splitPrepareScan, Cfg.ofWords, stateWord]
      funext z
      simp [catalogPolyTape]
  have hfirst : (splitPrepareTM k).tm.runFrom (splitPrepareScan k w s 0) (s.length + 1) =
      splitPrepareReady k w s 1 (s.length - 1) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', splitPrepare_scan k w s _ (le_refl _), splitPrepare_extra]
  rw [hinit, show 2 * (s.length + 1) = (s.length + 1) + (s.length + 1) by omega,
    MultiTapeTM.runFrom_add, hfirst, splitPrepare_rewind k w s s.length (le_refl _)]

/-- A phase trace excludes the round anchor even at its two endpoints. -/
private def splitSafe {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c : Cfg k Bool S w) (t : ℕ) : Prop :=
  ∀ j ≤ t, (tm.runFrom c j).state ≠ some anchor

/-- Safe traces concatenate at their literal configuration seam. -/
private lemma splitSafe_add {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c : Cfg k Bool S w) (u v : ℕ)
    (hu : splitSafe tm anchor c u) (hv : splitSafe tm anchor (tm.runFrom c u) v) :
    splitSafe tm anchor c (u + v) := by
  intro j hj
  by_cases h : j ≤ u
  · exact hu j h
  · have he : j = u + (j - u) := by omega
    rw [he, MultiTapeTM.runFrom_add]
    exact hv (j - u) (by omega)

/-- Cut an absorbing source phase at its first terminal control state and
embed the entire prefix into a disjoint host phase.
**Proof sketch.** Take the least terminal visit. Absorption identifies its
configuration with the known endpoint. Induct on the prefix length using
transition agreement only before that visit; every mapped control state,
including a halted state, is different from the host anchor. -/
private lemma splitEmbed_cut {k : ℕ} {S H : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (host : MultiTapeTM k Bool H)
    (emb : S → H) (anchor : H) (stop : S → Prop) [DecidablePred stop]
    (haway : ∀ q, emb q ≠ anchor)
    (hfix : ∀ c : Cfg k Bool S w, (∃ q, c.state = some q ∧ stop q) → tm.step c = c)
    (hagree : ∀ q, ¬stop q → ∀ inp work,
      host.tr (emb q) inp work = (tm.tr q inp work).mapState emb)
    (c d : Cfg k Bool S w) (T : ℕ)
    (hd : ∃ q, d.state = some q ∧ stop q) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, host.runFrom (c.mapState emb) t = d.mapState emb ∧
      splitSafe host anchor (c.mapState emb) t := by
  classical
  have hex : ∃ t, ∃ q, (tm.runFrom c t).state = some q ∧ stop q :=
    ⟨T, by rw [hT]; exact hd⟩
  let t := Nat.find hex
  have ht : t ≤ T := Nat.find_min' hex (by rw [hT]; exact hd)
  have he : tm.runFrom c t = d := by
    have hh := tm.runFrom_add c t (T - t)
    have hconst : tm.runFrom (tm.runFrom c t) (T - t) = tm.runFrom c t :=
      Function.iterate_fixed (hfix _ (Nat.find_spec hex)) _
    rw [Nat.add_sub_of_le ht, hT, hconst] at hh
    exact hh.symm
  have hp : ∀ j ≤ t, host.runFrom (c.mapState emb) j = (tm.runFrom c j).mapState emb := by
    intro j
    induction j with
    | zero => intro hj; rfl
    | succ j ih =>
      intro hj
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
        MultiTapeTM.runFrom_succ_eq_step']
      let z := tm.runFrom c j
      change host.step (z.mapState emb) = (tm.step z).mapState emb
      cases hz : z.state with
      | none => simp [MultiTapeTM.step, Cfg.mapState, hz]
      | some q =>
        have hn : ¬stop q := fun hq => Nat.find_min hex (by omega) ⟨q, hz, hq⟩
        simp only [MultiTapeTM.step, Cfg.mapState, hz, Option.map_some]
        rw [hagree q hn]
        rfl
  refine ⟨t, ht, by rw [hp t (le_refl _), he], ?_⟩
  intro j hj
  rw [hp j hj]
  cases hs : (tm.runFrom c j).state with
  | none => simp [Cfg.mapState, hs]
  | some q => simpa [Cfg.mapState, hs] using haway q

/-- A standalone native-input rewind, with an absorbing return at state two. -/
private def splitRewindTM (k : ℕ) : FinTM Bool where
  k := k + 1
  State := Fin 3
  tm := {
    q₀ := 0
    tr := fun q inp _ => match q.val with
      | 0 => controlAction .neg (some 1)
      | 1 => match inp with
        | some _ => controlAction .neg (some 1)
        | none => controlAction .pos (some 2)
      | _ => controlAction 0 (some 2) }

/-- Emit a native-input split, using tape zero only as a length counter.
The first two states double native bits, state two completes the separator,
and state three copies the native suffix. No candidate bit is emitted. -/
private def splitEmitTM (k : ℕ) : FinTM Bool where
  k := k + 1
  State := Fin 4
  tm := {
    q₀ := 0
    tr := fun q inp work => match q.val with
      | 0 => match work 0 with
        | none => ⟨0, fun _ => (none, 0), some false, some 2⟩
        | some _ => ⟨0, fun _ => (none, 0), inp, some 1⟩
      | 1 => ⟨.pos, Fin.cases (none, .pos) (fun _ => (none, 0)), inp, some 0⟩
      | 2 => ⟨0, fun _ => (none, 0), some true, some 3⟩
      | _ => match inp with
        | some b => ⟨.pos, fun _ => (none, 0), some b, some 3⟩
        | none => controlAction 0 none }

/-- Each subroutine has its own finite control phase; only cleanup can
return to the anchor. The acceptance bit survives the native-input rewind. -/
private inductive SplitBodyState (S : Type) where
  | anchor
  | prepare (q : Fin 3 × Bool)
  | count (q : S) (over : Bool)
  | check (over : Bool)
  | rewind (accept : Bool) (q : Fin 3)
  | restore (q : Fin 5 × Bool)
  | emit (q : Fin 4)

private instance splitBodyStateFintype (S : Type) [Fintype S] :
    Fintype (SplitBodyState S) := derive_fintype% _

/-- Equality of controller states compares only matching phases and their
finite payloads. Keep the instance private, including its generated helpers. -/
private instance splitBodyStateDecidableEq (S : Type) [DecidableEq S] :
    DecidableEq (SplitBodyState S) := by
  intro a b
  cases a <;> cases b
  all_goals try (solve | apply isFalse; intro h; cases h)
  · exact isTrue rfl
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (SplitBodyState.prepare.injEq _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (SplitBodyState.count.injEq _ _ _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (SplitBodyState.check.injEq _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (SplitBodyState.rewind.injEq _ _ _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (SplitBodyState.restore.injEq _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (SplitBodyState.emit.injEq _ _)))

/-- Combined round controller. The polynomial source starts on the prepared
bank, and its emissions are counted against native input without physical
output. Every seam transition is explicit, including the final anchor return. -/
private def splitBodyTM (M : FinTM Bool) (start : M.State) : FinTM Bool where
  k := M.k + 1
  State := SplitBodyState M.State
  tm := {
    q₀ := .anchor
    tr := fun q inp work => match q with
      | .anchor => controlAction 0 (some (.prepare (0, false)))
      | .prepare p =>
        if p.1 = 2 then controlAction 0 (some (.count start p.2))
        else ((splitPrepareTM M.k).tm.tr p inp work).mapState .prepare
      | .count q over => splitCountAction .count .check over inp
          (M.tm.tr q none (fun i => work i.succ))
      | .check over => controlAction 0 (some (.rewind (!over && inp.isNone) 0))
      | .rewind ok p =>
        if p = 2 then controlAction 0 (some (if ok then .emit 0 else .restore (0, false)))
        else ((splitRewindTM M.k).tm.tr p inp work).mapState (.rewind ok)
      | .restore p =>
        if p = (4, false) then controlAction 0 (some .anchor)
        else ((splitRestoreTM M.k).tm.tr p inp work).mapState .restore
      | .emit p => ((splitEmitTM M.k).tm.tr p inp work).mapState .emit }

/-- **The padding split search**. The find-mode loop host over the split-search body, fuelled by the
binary length counter: the round state is a candidate `i` in unary, and each round evaluates
`C·(i + 1)^e` in unary by the source of today's case split (the prepending machine of
`List.replicate C true` for `e = 0`, the unary engine for `e = d + 1`), compares `i + C·(i + 1)^e`
with `|w|`, and either emits `pairEncode (w.take i) (w.drop i)` or advances. -/
def splitSolveTM (C : ℕ) : ℕ → FinTM Bool
  | 0 => loopHostTM (splitBodyTM (prependTM (List.replicate C true))
      (0 : Fin ((List.replicate C true).length + 1))) lengthBitsTM .anchor true
  | e + 1 => loopHostTM (splitBodyTM (catalogPolyUnaryTM e C) (.loop (Fin.last e)))
      lengthBitsTM .anchor true

/-- The source bank has the candidate's successor length on each tape and
all heads at zero; its virtual input is empty. -/
private def splitBank (M : FinTM Bool) (s : List Bool)
    (q : Option M.State) (out : List Bool) : Cfg M.k Bool M.State [] :=
  ⟨q, 1, fun _ => catalogPolyTape (s.length + 1), fun _ => 0, out⟩

/-- The genuine initial configuration is the empty-candidate anchor seam;
there is no unproved startup work hidden in a zero-time witness. -/
private lemma splitBody_start (M : FinTM Bool) (start : M.State) (w : List Bool) :
    (splitBodyTM M start).tm.initCfg w =
      Cfg.ofWords .anchor (stateWord (M.k + 1) []) := by
  rw [initCfg_ofWords]
  congr 1
  funext i
  simp [stateWord]

/-- Preparation reaches its first return with the exact counted-source bank.
Every configuration of the embedded preparation is outside the anchor phase.
**Proof sketch.** Cut the absorbing source at its first return, map its full
configuration into the preparation phase, then take the explicit dispatch.
Check the source-bank seam field by field, including the native head and flag. -/
private lemma splitBody_prepare (M : FinTM Bool) (start : M.State) (w s : List Bool) :
    ∃ t ≤ 2 * (s.length + 1),
      (splitBodyTM M start).tm.runFrom
        (Cfg.ofWords (.prepare (0, false)) (stateWord (M.k + 1) s)) (t + 1) =
          splitCountCfg SplitBodyState.count SplitBodyState.check w s
            (splitBank M s (some start) []) ∧
      splitSafe (splitBodyTM M start).tm .anchor
        (Cfg.ofWords (input := w) (.prepare (0, false)) (stateWord (M.k + 1) s)) (t + 1) := by
  obtain ⟨t, ht, he, hsafe⟩ := splitEmbed_cut (splitPrepareTM M.k).tm
    (splitBodyTM M start).tm SplitBodyState.prepare .anchor (fun q => q.1 = 2)
    (by intro q; simp)
    (by
      rintro z ⟨⟨q, over⟩, hz, hq⟩
      change q = 2 at hq
      subst q
      simp only [MultiTapeTM.step, hz]
      change (controlAction 0 (some (2, over))).apply z = z
      rw [controlAction_apply, moveInputPos_zero]
      cases z; simp_all)
    (by intro q hq inp work; simp [splitBodyTM, hq])
    (Cfg.ofWords (input := w) (0, false) (stateWord (M.k + 1) s))
    (splitPrepareReady M.k w s 2 0) (2 * (s.length + 1))
    ⟨_, rfl, rfl⟩ (splitPrepare_run M.k w s)
  have hstep : (splitBodyTM M start).tm.step
      ((splitPrepareReady M.k w s 2 0).mapState SplitBodyState.prepare) =
      splitCountCfg SplitBodyState.count SplitBodyState.check w s
        (splitBank M s (some start) []) := by
    simp only [MultiTapeTM.step, Cfg.mapState, splitPrepareReady, Option.map_some,
      splitBodyTM, ↓reduceIte]
    refine Cfg.ext ?_ ?_ rfl ?_ rfl
    · simp [Action.apply, controlAction, splitCountCfg, splitBank]
    · simp [Action.apply, controlAction, splitCountCfg, splitBank]
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp [Action.apply, controlAction, splitCountCfg, splitBank]
  have hinit : (Cfg.ofWords (input := w) (0, false) (stateWord (M.k + 1) s)).mapState
      (SplitBodyState.prepare (S := M.State)) = Cfg.ofWords (.prepare (0, false)) (stateWord (M.k + 1) s) := rfl
  rw [hinit] at he hsafe
  have hend : (splitBodyTM M start).tm.runFrom
      (Cfg.ofWords (.prepare (0, false)) (stateWord (M.k + 1) s)) (t + 1) =
      splitCountCfg SplitBodyState.count SplitBodyState.check w s
        (splitBank M s (some start) []) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', he, hstep]
  refine ⟨t, ht, hend, ?_⟩
  intro j hj
  by_cases hjt : j ≤ t
  · exact hsafe j hjt
  · have hj' : j = t + 1 := by omega
    rw [hj', hend]
    simp [splitCountCfg, splitBank]

/-- Counted evaluation reaches its first source halt; every prefix remains
in a count or check state and therefore cannot revisit the round anchor.
**Proof sketch.** Choose the least source halt and remove its constant halted
suffix. Apply the counted correspondence to every prefix through that halt;
its control image is disjoint from the anchor, including the return state. -/
private lemma splitBody_count (M : FinTM Bool) (start : M.State) (w s : List Bool)
    (out : List Bool) (T : ℕ)
    (hT : M.tm.runFrom (splitBank M s (some start) []) T = splitBank M s none out) :
    ∃ t ≤ T, (splitBodyTM M start).tm.runFrom
      (splitCountCfg SplitBodyState.count SplitBodyState.check w s (splitBank M s (some start) [])) t =
      splitCountCfg SplitBodyState.count SplitBodyState.check w s (splitBank M s none out) ∧
      splitSafe (splitBodyTM M start).tm .anchor
        (splitCountCfg SplitBodyState.count SplitBodyState.check w s (splitBank M s (some start) [])) t := by
  classical
  let c := splitBank M s (some start) []
  let d := splitBank M s none out
  have hh : ∃ t, (M.tm.runFrom c t).state = none := ⟨T, by rw [hT]; rfl⟩
  let t := Nat.find hh
  have ht : t ≤ T := Nat.find_min' hh (by rw [hT]; rfl)
  have he : M.tm.runFrom c t = d := by
    have h := M.tm.runFrom_add c t (T - t)
    rw [Nat.add_sub_of_le ht, hT, M.tm.runFrom_of_halt _ (Nat.find_spec hh)] at h
    exact h.symm
  have hp (j : ℕ) (hj : j ≤ t) := splitCount_run M.tm (splitBodyTM M start).tm
    SplitBodyState.count SplitBodyState.check (fun _ _ _ _ => rfl) w s c j
    (fun l hl => Nat.find_min hh (by omega))
  refine ⟨t, ht, ?_, ?_⟩
  · rw [hp t (le_refl _), he]
  · intro j hj
    rw [hp j hj]
    cases hq : (M.tm.runFrom c j).state <;> simp [splitCountCfg, hq]

/-- Rewind preserves the exact source bank and physical output. Its terminal
state is cut before dispatch to the accepting emitter or rejecting cleanup.
**Proof sketch.** Use the quantitative native rewind, then cut its absorbing
return and embed that prefix while retaining the acceptance bit in control. -/
private lemma splitBody_rewind (M : FinTM Bool) (start : M.State) (w : List Bool)
    (ok : Bool) (c : Cfg (M.k + 1) Bool (Fin 3) w)
    (hc : c.state = some 0) :
    ∃ t ≤ c.inputPos.val + 2,
      (splitBodyTM M start).tm.runFrom (c.mapState (SplitBodyState.rewind ok)) t =
        ({c with state := some (2 : Fin 3), inputPos := 1}).mapState (SplitBodyState.rewind ok) ∧
      splitSafe (splitBodyTM M start).tm .anchor (c.mapState (SplitBodyState.rewind ok)) t := by
  obtain ⟨T, hT, he⟩ := catalogRewind (splitRewindTM M.k).tm (0 : Fin 3) (1 : Fin 3) (some (2 : Fin 3))
    (fun _ _ => rfl) (fun _ _ => rfl) c hc
  obtain ⟨t, ht, hend, hsafe⟩ := splitEmbed_cut (splitRewindTM M.k).tm
    (splitBodyTM M start).tm (SplitBodyState.rewind ok) .anchor (fun q => q = (2 : Fin 3))
    (by intro q; simp)
    (by
      rintro z ⟨q, hz, rfl⟩
      simp only [MultiTapeTM.step, hz]
      change (controlAction 0 (some (2 : Fin 3))).apply z = z
      rw [controlAction_apply, moveInputPos_zero]
      cases z; simp_all)
    (by intro q hq inp work; simp [splitBodyTM, hq])
    c {c with state := some (2 : Fin 3), inputPos := 1} T ⟨(2 : Fin 3), rfl, rfl⟩ he
  exact ⟨t, ht.trans hT, hend, hsafe⟩

/-- Rejection cleanup is embedded up to its absorbing return, so its exact
restoration and the no-anchor property hold simultaneously in the body.
**Proof sketch.** Apply the exact restoration run and cut at its absorbing
false-flag return. Its host control remains in the restore phase; the final
transition to the anchor is accounted for separately by the round proof. -/
private lemma splitBody_restore (M : FinTM Bool) (start : M.State) (w s : List Bool) :
    ∃ t ≤ 2 * s.length + w.length + 5,
      (splitBodyTM M start).tm.runFrom
        ((splitRestoreScan M.k w s 0).mapState SplitBodyState.restore) t =
        Cfg.ofWords (.restore (4, false)) (stateWord (M.k + 1) (splitStep w s)) ∧
      splitSafe (splitBodyTM M start).tm .anchor
        ((splitRestoreScan M.k w s 0).mapState SplitBodyState.restore) t := by
  obtain ⟨T, hT, he⟩ := splitRestore_run M.k w s
  obtain ⟨t, ht, hend, hsafe⟩ := splitEmbed_cut (splitRestoreTM M.k).tm
    (splitBodyTM M start).tm SplitBodyState.restore .anchor (fun q => q = (4, false))
    (by intro q; simp)
    (by
      rintro z ⟨q, hz, rfl⟩
      simp only [MultiTapeTM.step, hz]
      change (controlAction 0 (some (4, false))).apply z = z
      rw [controlAction_apply, moveInputPos_zero]
      cases z; simp_all)
    (by intro q hq inp work; simp [splitBodyTM, hq])
    (splitRestoreScan M.k w s 0)
    (Cfg.ofWords (4, false) (stateWord (M.k + 1) (splitStep w s))) T
    ⟨_, rfl, rfl⟩ he
  exact ⟨t, ht.trans hT, hend, hsafe⟩

/-- Emitter configurations preserve the initialized scratch bank and use the
candidate head only to count the doubled native prefix. -/
private def splitEmitCfg (k : ℕ) (w s : List Bool) (q : Option (Fin 4))
    (j h : ℕ) (out : List Bool) : Cfg (k + 1) Bool (Fin 4) w :=
  ⟨q, splitPos w j, Fin.cases (bufferTape s) (fun _ => catalogPolyTape (s.length + 1)),
    Fin.cases (h : ℤ) (fun _ => 0), out⟩

/-- Two transitions emit two copies of the current native bit and advance
both the native head and the candidate counter. Arbitrary candidate bit
values are read only for their presence.
**Proof sketch.** Induct on the number of doubled cells. The two transitions
read the same native bit, emit it twice, and only then advance both heads. -/
private lemma splitEmit_double (k : ℕ) (w s : List Bool) (hs : s.length ≤ w.length) :
    ∀ j, j ≤ s.length → (splitEmitTM k).tm.runFrom
      (splitEmitCfg k w s (some 0) 0 0 []) (2 * j) =
      splitEmitCfg k w s (some 0) j j ((w.take j).flatMap fun b => [b, b]) := by
  intro j
  induction j with
  | zero => intro hj; rfl
  | succ j ih =>
    intro hj
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hread (q : Fin 4) (out : List Bool) :
        (splitEmitCfg k w s (some q) j j out).inputSymbol = some (w[j]'(by omega)) := by
      rw [splitPos_read w _ j rfl, dif_pos (by omega)]
    have hwork : (splitEmitCfg k w s (some 0) j j
        ((w.take j).flatMap fun b => [b, b])).workTapeSymbols 0 = some (s[j]'(by omega)) := by
      simp [splitEmitCfg, Cfg.workTapeSymbols, List.getElem?_eq_getElem (by omega : j < s.length)]
    have hfirst : (splitEmitTM k).tm.step
        (splitEmitCfg k w s (some 0) j j ((w.take j).flatMap fun b => [b, b])) =
        splitEmitCfg k w s (some 1) j j
          (((w.take j).flatMap fun b => [b, b]) ++ [w[j]'(by omega)]) := by
      unfold MultiTapeTM.step
      change ((splitEmitTM k).tm.tr (0 : Fin 4) _ _).apply _ = _
      simp only [splitEmitTM, hwork, hread]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; simp [Action.apply, splitEmitCfg]
    rw [hfirst]
    unfold MultiTapeTM.step
    change ((splitEmitTM k).tm.tr (1 : Fin 4) _ _).apply _ = _
    simp only [splitEmitTM, hread]
    refine Cfg.ext rfl (splitPos_succ w j) ?_ ?_ ?_
    · funext i
      refine Fin.cases ?_ (fun l => ?_) i <;> rfl
    · funext i
      refine Fin.cases ?_ (fun l => ?_) i <;> simp [Action.apply, splitEmitCfg]
    · change (((w.take j).flatMap fun b => [b, b]) ++ [w[j]'(by omega)]) ++
          [w[j]'(by omega)] = (w.take (j + 1)).flatMap fun b => [b, b]
      simp only [List.take_succ, List.getElem?_eq_getElem (by omega : j < w.length),
        Option.toList_some, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- Once the counter is exhausted, emit the two separator bits without
moving the native head away from the beginning of the suffix. -/
private lemma splitEmit_separator (k : ℕ) (w s : List Bool) (out : List Bool) :
    (splitEmitTM k).tm.runFrom (splitEmitCfg k w s (some 0) s.length s.length out) 2 =
      splitEmitCfg k w s (some 3) s.length s.length (out ++ [false, true]) := by
  have hwork : (splitEmitCfg k w s (some 0) s.length s.length out).workTapeSymbols 0 = none := by
    simp [splitEmitCfg, Cfg.workTapeSymbols]
  have hf : (splitEmitTM k).tm.step (splitEmitCfg k w s (some 0) s.length s.length out) =
      splitEmitCfg k w s (some 2) s.length s.length (out ++ [false]) := by
    unfold MultiTapeTM.step
    change ((splitEmitTM k).tm.tr (0 : Fin 4) _ _).apply _ = _
    simp only [splitEmitTM, hwork]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply, splitEmitCfg]
  rw [show 2 = 1 + 1 by omega, MultiTapeTM.runFrom_succ_eq_step,
    show (splitEmitTM k).tm.step _ = _ from hf, MultiTapeTM.runFrom_succ_eq_step,
    MultiTapeTM.runFrom_zero]
  refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
  · funext i; simp [MultiTapeTM.step, splitEmitTM, Action.apply, splitEmitCfg]
  · simp [MultiTapeTM.step, splitEmitTM, Action.apply, splitEmitCfg, List.append_assoc]

/-- The suffix-copy phase preserves all work tapes and copies native bits
verbatim, including the empty suffix and its final blank-reading halt.
**Proof sketch.** Induct on the remaining suffix while allowing arbitrary
already-copied prefix and output. The nonempty case copies one native bit;
the empty case reads the right blank and halts without an extra emission. -/
private lemma splitEmit_suffix (k : ℕ) (w s rest : List Bool) :
    ∀ pre out h, w = pre ++ rest → (splitEmitTM k).tm.runFrom
      (splitEmitCfg k w s (some 3) pre.length h out) (rest.length + 1) =
      splitEmitCfg k w s none w.length h (out ++ rest) := by
  induction rest with
  | nil =>
    intro pre out h hw
    have he : w = pre := by simpa using hw
    clear hw
    subst w
    simp only [List.append_nil, List.length_nil, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_zero]
    have hr := splitPos_read pre (splitEmitCfg k pre s (some 3) pre.length h out) pre.length rfl
    simp only [Nat.lt_irrefl, ↓reduceDIte] at hr
    unfold MultiTapeTM.step
    change ((splitEmitTM k).tm.tr (3 : Fin 4) _ _).apply _ = _
    rw [hr]
    simp [splitEmitTM, controlAction, splitEmitCfg]
  | cons b rest ih =>
    intro pre out h hw
    have hread : (splitEmitCfg k w s (some 3) pre.length h out).inputSymbol = some b := by
      rw [splitPos_read w _ pre.length rfl]
      simp [hw]
    have hstep : (splitEmitTM k).tm.step (splitEmitCfg k w s (some 3) pre.length h out) =
        splitEmitCfg k w s (some 3) (pre ++ [b]).length h (out ++ [b]) := by
      unfold MultiTapeTM.step
      change ((splitEmitTM k).tm.tr (3 : Fin 4) _ _).apply _ = _
      rw [hread]
      refine Cfg.ext rfl ?_ rfl ?_ rfl
      · simpa only [List.length_append, List.length_singleton] using splitPos_succ w pre.length
      · funext i; simp [splitEmitTM, Action.apply, splitEmitCfg]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [b]) (out ++ [b]) h (by simpa [List.append_assoc] using hw)

/-- The accepting emitter produces exactly the encoded native split in
`|s|+|w|+3` steps. Its candidate may contain any bit pattern.
**Proof sketch.** Double exactly the native prefix counted by the candidate,
emit the separator, and copy the remaining native suffix. Concatenate the
three exact runs and cancel the prefix length in the time expression. -/
private lemma splitEmit_run (k : ℕ) (w s : List Bool) (hs : s.length ≤ w.length) :
    (splitEmitTM k).tm.runFrom (splitEmitCfg k w s (some 0) 0 0 [])
      (s.length + w.length + 3) =
      splitEmitCfg k w s none w.length s.length
        (pairEncode (w.take s.length) (w.drop s.length)) := by
  have ht : s.length + w.length + 3 =
      2 * s.length + 2 + ((w.drop s.length).length + 1) := by
    simp only [List.length_drop]; omega
  rw [ht, MultiTapeTM.runFrom_add,
    MultiTapeTM.runFrom_add _ (2 * s.length) 2,
    splitEmit_double k w s hs _ (le_refl _), splitEmit_separator]
  have h := splitEmit_suffix k w s (w.drop s.length) (w.take s.length)
    (((w.take s.length).flatMap fun b => [b, b]) ++ [false, true]) s.length
    (List.take_append_drop s.length w).symm
  simpa [List.length_take, Nat.min_eq_left hs, pairEncode] using h

/-- A single transition is safe when both its endpoints exclude the anchor. -/
private lemma splitSafe_one {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c d : Cfg k Bool S w)
    (he : tm.step c = d) (hc : c.state ≠ some anchor) (hd : d.state ≠ some anchor) :
    tm.runFrom c 1 = d ∧ splitSafe tm anchor c 1 := by
  refine ⟨he, ?_⟩
  intro j hj
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
  · exact hc
  · change (tm.step c).state ≠ _
    rw [he]; exact hd

/-- Concatenate two safe exact phase runs. -/
private lemma splitSafe_join {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c d f : Cfg k Bool S w) (u v : ℕ)
    (h1 : tm.runFrom c u = d) (hs1 : splitSafe tm anchor c u)
    (h2 : tm.runFrom d v = f) (hs2 : splitSafe tm anchor d v) :
    tm.runFrom c (u + v) = f ∧ splitSafe tm anchor c (u + v) := by
  refine ⟨by rw [MultiTapeTM.runFrom_add, h1, h2], ?_⟩
  apply splitSafe_add tm anchor c u v hs1
  rw [h1]; exact hs2

/-- A completed source gives a complete body round, including acceptance,
rejection, positive duration, and anchor exclusion over every strict interior
step. The bound explicitly includes all dispatches, rewinds, and emission.
**Proof sketch.** Depart the anchor in one step. Concatenate safe preparation,
counting, decision, and rewind traces. Equality accepts and emits native
slices. Inequality dispatches to the exact scratch restoration, followed by
one explicit return to the anchor. All intermediate states belong to disjoint
phases; the only anchor step is the final rejecting transition. -/
private lemma splitBody_round (M : FinTM Bool) (start : M.State) (w s out : List Bool)
    (T : ℕ) (hT : M.tm.runFrom (splitBank M s (some start) []) T = splitBank M s none out) :
    ∃ t, 0 < t ∧ t ≤ T + 5 * s.length + 3 * w.length + 20 ∧
      (∀ j, 0 < j → j < t →
        ((splitBodyTM M start).tm.runFrom
          (Cfg.ofWords (input := w) .anchor (stateWord (M.k + 1) s)) j).state ≠ some .anchor) ∧
      if decide (s.length + out.length = w.length) then
        ((splitBodyTM M start).tm.runFrom
          (Cfg.ofWords (input := w) .anchor (stateWord (M.k + 1) s)) t).state = none ∧
        ((splitBodyTM M start).tm.runFrom
          (Cfg.ofWords (input := w) .anchor (stateWord (M.k + 1) s)) t).output =
            pairEncode (w.take s.length) (w.drop s.length)
      else (splitBodyTM M start).tm.runFrom
        (Cfg.ofWords (input := w) .anchor (stateWord (M.k + 1) s)) t =
          Cfg.ofWords .anchor (stateWord (M.k + 1) (splitStep w s)) := by
  let tm := (splitBodyTM M start).tm
  let z : Cfg (M.k + 1) Bool (SplitBodyState M.State) w :=
    Cfg.ofWords .anchor (stateWord (M.k + 1) s)
  let p : Cfg (M.k + 1) Bool (SplitBodyState M.State) w :=
    Cfg.ofWords (.prepare (0, false)) (stateWord (M.k + 1) s)
  let d := splitCountCfg SplitBodyState.count SplitBodyState.check w s (splitBank M s none out)
  let ok := decide (s.length + out.length = w.length)
  let c : Cfg (M.k + 1) Bool (Fin 3) w :=
    ⟨some 0, splitPos w (s.length + out.length),
      Fin.cases (bufferTape s) (fun _ => catalogPolyTape (s.length + 1)),
      Fin.cases 0 (fun _ => 0), []⟩
  let r : Cfg (M.k + 1) Bool (SplitBodyState M.State) w :=
    ({c with state := some (2 : Fin 3), inputPos := 1} : Cfg (M.k + 1) Bool (Fin 3) w).mapState
    (SplitBodyState.rewind (S := M.State) ok)
  have hdepart : tm.runFrom z 1 = p := by
    change (controlAction 0 (some (.prepare (0, false)))).apply z = p
    rw [controlAction_apply, moveInputPos_zero]
    rfl
  obtain ⟨a, ha, hprep, hpreps⟩ := splitBody_prepare M start w s
  obtain ⟨b, hb, hcount, hcounts⟩ := splitBody_count M start w s out T hT
  obtain ⟨h1, hs1⟩ := splitSafe_join tm .anchor p _ d (a + 1) b hprep hpreps hcount hcounts
  have hcheck : tm.step d = c.mapState (SplitBodyState.rewind ok) := by
    unfold MultiTapeTM.step
    change (controlAction 0 (some (.rewind
      (!decide (w.length < s.length + out.length) && d.inputSymbol.isNone) 0))).apply d = _
    rw [controlAction_apply, moveInputPos_zero]
    have hok := splitCount_accept SplitBodyState.count SplitBodyState.check w s
      (splitBank M s none out)
    change (!decide (w.length < s.length + out.length) && d.inputSymbol.isNone) = ok at hok
    rw [hok]
    rfl
  obtain ⟨hcheck', hchecks⟩ := splitSafe_one tm .anchor d _ hcheck
    (by simp [d, splitCountCfg, splitBank]) (by simp [c, Cfg.mapState])
  obtain ⟨h2, hs2⟩ := splitSafe_join tm .anchor p d _ (a + 1 + b) 1 h1 hs1 hcheck' hchecks
  obtain ⟨v, hv, hrew, hrews⟩ := splitBody_rewind M start w ok c rfl
  obtain ⟨h3, hs3⟩ := splitSafe_join tm .anchor p _ r (a + 1 + b + 1) v h2 hs2 hrew hrews
  have hv' : v ≤ w.length + 3 := by
    have hp : c.inputPos.val ≤ w.length + 1 := by simp [c, splitPos]
    omega
  by_cases hok : s.length + out.length = w.length
  · have hs : s.length ≤ w.length := by omega
    let ec := splitEmitCfg M.k w s (some 0) 0 0 []
    let ed := splitEmitCfg M.k w s none w.length s.length
      (pairEncode (w.take s.length) (w.drop s.length))
    have hdispatch : tm.step r = ec.mapState SplitBodyState.emit := by
      simp only [r, c, Cfg.mapState, Option.map_some, MultiTapeTM.step,
        tm, splitBodyTM, ↓reduceIte, ok, hok, decide_true]
      rw [controlAction_apply, moveInputPos_zero]
      refine Cfg.ext rfl ?_ rfl rfl rfl
      simp [ec, splitEmitCfg, splitPos]
    obtain ⟨hd, hds⟩ := splitSafe_one tm .anchor r _ hdispatch
      (by simp [r, Cfg.mapState]) (by simp [ec, Cfg.mapState, splitEmitCfg])
    obtain ⟨h4, hs4⟩ := splitSafe_join tm .anchor p r _ (a + 1 + b + 1 + v) 1 h3 hs3 hd hds
    have transport (j : ℕ) : tm.runFrom (ec.mapState SplitBodyState.emit) j =
        ((splitEmitTM M.k).tm.runFrom ec j).mapState SplitBodyState.emit :=
      MultiTapeTM.runFrom_mapState_of_agreeOn (splitEmitTM M.k).tm tm
        ⟨SplitBodyState.emit, by intro a b h; exact SplitBodyState.emit.inj h⟩
        (fun _ => True) (fun _ _ _ _ => rfl) ec j (by intros; trivial)
    have hemit : tm.runFrom (ec.mapState SplitBodyState.emit) (s.length + w.length + 3) =
        ed.mapState SplitBodyState.emit := by
      rw [transport]
      exact congrArg (Cfg.mapState SplitBodyState.emit) (splitEmit_run M.k w s hs)
    have hemits : splitSafe tm .anchor (ec.mapState SplitBodyState.emit) (s.length + w.length + 3) := by
      intro j hj
      rw [transport]
      cases hq : ((splitEmitTM M.k).tm.runFrom ec j).state <;> simp [Cfg.mapState, hq]
    obtain ⟨h5, hs5⟩ := splitSafe_join tm .anchor p _ _ (a + 1 + b + 1 + v + 1)
      (s.length + w.length + 3) h4 hs4 hemit hemits
    let u := a + 1 + b + 1 + v + 1 + (s.length + w.length + 3)
    have hend : tm.runFrom z (1 + u) = ed.mapState SplitBodyState.emit := by
      rw [MultiTapeTM.runFrom_add, hdepart]; exact h5
    refine ⟨1 + u, by omega, by dsimp [u]; omega, ?_, ?_⟩
    · intro j hj hjt
      change (tm.runFrom z j).state ≠ _
      rw [show j = 1 + (j - 1) by omega, MultiTapeTM.runFrom_add, hdepart]
      exact hs5 (j - 1) (by dsimp [u] at hjt; omega)
    · simp only [hok, decide_true, ↓reduceIte]
      change (tm.runFrom z (1 + u)).state = none ∧ _
      rw [hend]
      exact ⟨rfl, rfl⟩
  · let rc := (splitRestoreScan M.k w s 0).mapState (SplitBodyState.restore (S := M.State))
    have hdispatch : tm.step r = rc := by
      simp only [r, c, Cfg.mapState, Option.map_some, MultiTapeTM.step,
        tm, splitBodyTM, ↓reduceIte, ok, hok, decide_false, Bool.false_eq_true]
      rw [controlAction_apply, moveInputPos_zero]
      refine Cfg.ext ?_ ?_ ?_ ?_ rfl
      · simp [rc, splitRestoreScan, Cfg.mapState]
      · simp [rc, splitRestoreScan, Cfg.mapState, splitPos]
      · funext i
        refine Fin.cases ?_ (fun l => ?_) i
        · rfl
        · funext z; simp [rc, splitRestoreScan, Cfg.mapState, splitScratch, catalogPolyTape]
      · funext i
        refine Fin.cases ?_ (fun l => ?_) i <;> rfl
    obtain ⟨hd, hds⟩ := splitSafe_one tm .anchor r rc hdispatch
      (by simp [r, Cfg.mapState]) (by simp [rc, Cfg.mapState, splitRestoreScan])
    obtain ⟨h4, hs4⟩ := splitSafe_join tm .anchor p r rc (a + 1 + b + 1 + v) 1 h3 hs3 hd hds
    obtain ⟨l, hl, hrest, hrests⟩ := splitBody_restore M start w s
    obtain ⟨h5, hs5⟩ := splitSafe_join tm .anchor p rc _ (a + 1 + b + 1 + v + 1) l h4 hs4 hrest hrests
    let u := a + 1 + b + 1 + v + 1 + l
    have hreturn : tm.step (Cfg.ofWords (.restore (4, false)) (stateWord (M.k + 1) (splitStep w s))) =
        Cfg.ofWords (input := w) .anchor (stateWord (M.k + 1) (splitStep w s)) := by
      change (controlAction 0 (some (SplitBodyState.anchor (S := M.State)))).apply _ = _
      rw [controlAction_apply, moveInputPos_zero]
      rfl
    refine ⟨1 + u + 1, by omega, by dsimp [u]; omega, ?_, ?_⟩
    · intro j hj hjt
      change (tm.runFrom z j).state ≠ _
      rw [show j = 1 + (j - 1) by omega, MultiTapeTM.runFrom_add, hdepart]
      exact hs5 (j - 1) (by dsimp [u] at hjt; omega)
    · simp only [hok, decide_false, Bool.false_eq_true, ↓reduceIte]
      change tm.runFrom z (1 + u + 1) = _
      rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add, hdepart, h5, hreturn]

/-- Given the concrete startup and round contracts, the audited loop supplies
the frozen split-search result and exponent. No body contract is assumed as an
axiom: both are explicit arguments, including the positive silent stall.
**Proof sketch.** Enlarge the body coefficient to cover the existing binary
length machine, instantiate the proved loop, identify its unary orbit and
finite search, then apply the checked exponent calculation. -/
private lemma splitSolve_of_body (C e : ℕ) (body : FinTM Bool) (anchor : body.State)
    (A : ℕ)
    (hstart : ∀ w : List Bool, ∃ t ≤ A * (w.length + 1) ^ (e + 1),
      (∀ t' < t, (body.tm.runFrom (body.tm.initCfg w) t').state ≠ some anchor) ∧
      body.tm.runFrom (body.tm.initCfg w) t =
        Cfg.ofWords anchor (stateWord body.k []))
    (hround : ∀ (w s : List Bool), s.length ≤ w.length + 1 →
      ∃ t, 0 < t ∧ t ≤ A * (w.length + 1) ^ (e + 1) ∧
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t').state
            ≠ some anchor) ∧
        if splitAccept C e w s then
          (body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t).state = none ∧
          (body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t).output =
            pairEncode (w.take s.length) (w.drop s.length)
        else
          body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t =
            Cfg.ofWords anchor (stateWord body.k (splitStep w s))) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun w => match solveSplit C e w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => []) (fun n => c * (n + 1) ^ (e + 2)) := by
  obtain ⟨F, a, hF⟩ := computesFunInTime_lengthBits
  have hn (n : ℕ) : n + 1 ≤ (n + 1) ^ (e + 1) := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos n)
      (show 1 ≤ e + 1 by omega)
  have hbody (n : ℕ) : A * (n + 1) ^ (e + 1) ≤ (A + a) * (n + 1) ^ (e + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have hF' : F.ComputesFunInTime (fun w => Nat.bits w.length)
      (fun n => (A + a) * (n + 1) ^ (e + 1)) := by
    intro w
    apply (hF w).mono
    exact (Nat.mul_le_mul_left a (hn w.length)).trans (Nat.mul_le_mul_right _ (by omega))
  obtain ⟨M, c, hM⟩ := exists_loopFindTM body F anchor
    (fun w s => s.length ≤ w.length + 1) splitStep (splitAccept C e)
    (fun w s => pairEncode (w.take s.length) (w.drop s.length)) (fun _ => [])
    id (fun n => (A + a) * (n + 1) ^ (e + 1)) hF'
    (by intro w; simp) splitStep_inv
    (by
      intro w
      obtain ⟨t, ht, hi, hh⟩ := hstart w
      exact ⟨t, ht.trans (hbody w.length), hi, hh⟩)
    (by
      intro w s hs
      obtain ⟨t, htpos, ht, hi, hh⟩ := hround w s hs
      exact ⟨t, htpos, ht.trans (hbody w.length), hi, hh⟩)
  refine ⟨M, 2 * c * (A + a + 1), fun w => ?_⟩
  have hm := hM w
  dsimp only [id_eq] at hm
  convert hm.mono (splitLoop_bound c (A + a) e w.length) using 1
  exact (splitLoop_result C e w).symm

/-- The positive-exponent source is the already proved nested-loop phase,
started on the prepared bank rather than rerunning input initialization. -/
private lemma splitSource_poly (c C : ℕ) (s : List Bool) :
    (catalogPolyUnaryTM c C).tm.runFrom
      (splitBank (catalogPolyUnaryTM c C) s (some (.loop (Fin.last c))) [])
      (catalogPolyCost (s.length + 1) C (c + 1) + 1) =
      splitBank (catalogPolyUnaryTM c C) s none
        (List.replicate (C * (s.length + 1) ^ (c + 1)) true) := by
  simpa [splitBank, catalogPolyCfg] using splitPoly_loop_end c C (s.length + 1) (by omega)

/-- Exponent zero uses the fixed prefix source on empty virtual input, with
no scratch tapes. Its last blank-reading step is included in the bound. -/
private lemma splitSource_constant (C : ℕ) (s : List Bool) :
    (prependTM (List.replicate C true)).tm.runFrom
      (splitBank (prependTM (List.replicate C true)) s
        (some (0 : Fin ((List.replicate C true).length + 1))) []) (C + 1) =
      splitBank (prependTM (List.replicate C true)) s none (List.replicate C true) := by
  have hi : splitBank (prependTM (List.replicate C true)) s
      (some (0 : Fin ((List.replicate C true).length + 1))) [] =
      (prependTM (List.replicate C true)).tm.initCfg [] := by
    apply Cfg.ext_zero_tapes <;> rfl
  rw [hi, MultiTapeTM.runFrom_succ_eq_step']
  have he := catalogPrefixTM_emit (List.replicate C true) [] C (by simp)
  rw [he]
  simp only [List.take_replicate, Nat.min_self]
  apply Cfg.ext_zero_tapes <;>
    simp [MultiTapeTM.step, prependTM, catalogPrefixCfg, Cfg.inputSymbol,
      Fin.ext_iff, Action.apply, splitBank]

/-- The invariant bounds every candidate, including the one-past-end stall,
inside one common body envelope. The factor `2^e` covers the prepared side
length `|s|+1 ≤ 2(|w|+1)` without increasing the exponent.
**Proof sketch.** Bound the source by its proved box cost, compare the two
side lengths, and absorb all linear controller overhead into forty copies of
the positive polynomial envelope. -/
private lemma splitBody_envelope (C e l n T : ℕ) (hl : l ≤ n + 1)
    (hT : T ≤ (C + 1 + 5 * e) * (l + 1) ^ e + 1) :
    T + 5 * l + 3 * n + 20 ≤
      ((C + 1 + 5 * e) * 2 ^ e + 40) * (n + 1) ^ (e + 1) := by
  have hp : (l + 1) ^ e ≤ 2 ^ e * (n + 1) ^ (e + 1) := by
    calc
      (l + 1) ^ e ≤ (2 * (n + 1)) ^ e := Nat.pow_le_pow_left (by omega) e
      _ = 2 ^ e * (n + 1) ^ e := Nat.mul_pow _ _ _
      _ ≤ 2 ^ e * (n + 1) ^ (e + 1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have hmul := Nat.mul_le_mul_left (C + 1 + 5 * e) hp
  have hn : n + 1 ≤ (n + 1) ^ (e + 1) := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos n)
      (show 1 ≤ e + 1 by omega)
  have hlin : 5 * l + 3 * n + 21 ≤ 40 * (n + 1) ^ (e + 1) := by omega
  calc
    T + 5 * l + 3 * n + 20 ≤
        (C + 1 + 5 * e) * (2 ^ e * (n + 1) ^ (e + 1)) +
          40 * (n + 1) ^ (e + 1) := by omega
    _ = _ := by ring

/-- Instantiate the completed controller with an exact unary-output source.
The source assumption is discharged below separately for zero and positive
exponents; startup and the full body round have already been constructed.
**Proof sketch.** Supply the exact zero-time startup and constructed round to
the existing loop closure. The common envelope bounds the actual phase times,
and the source's unary-output length identifies the checked acceptance test. -/
private lemma splitSolve_source (C e : ℕ) (M : FinTM Bool) (start : M.State)
    (B : ℕ → ℕ)
    (hsource : ∀ s : List Bool, M.tm.runFrom (splitBank M s (some start) []) (B s.length) =
      splitBank M s none (List.replicate (C * (s.length + 1) ^ e) true))
    (hbound : ∀ l, B l ≤ (C + 1 + 5 * e) * (l + 1) ^ e + 1) :
    ∃ (N : FinTM Bool) (c : ℕ),
      N.ComputesFunInTime
        (fun w => match solveSplit C e w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => []) (fun n => c * (n + 1) ^ (e + 2)) := by
  apply splitSolve_of_body C e (splitBodyTM M start) .anchor
    ((C + 1 + 5 * e) * 2 ^ e + 40)
  · intro w
    refine ⟨0, Nat.zero_le _, ?_, ?_⟩
    · intro j hj; omega
    · exact splitBody_start M start w
  · intro w s hs
    obtain ⟨t, htpos, ht, hsafe, hend⟩ := splitBody_round M start w s
      (List.replicate (C * (s.length + 1) ^ e) true) (B s.length) (hsource s)
    refine ⟨t, htpos, ht.trans (splitBody_envelope C e s.length w.length (B s.length)
      hs (hbound s.length)), hsafe, ?_⟩
    simpa only [splitAccept, List.length_replicate] using hend

/-- Close the two exponent cases privately, so compiler-generated proof
helpers also remain private. Both cases instantiate the concrete body and
its proved round contract through the exact source interfaces. -/
private lemma splitSolve_closed (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun w => match solveSplit C e w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => [])
        fun n => c * (n + 1) ^ (e + 2) := by
  cases e with
  | zero =>
    apply splitSolve_source C 0 (prependTM (List.replicate C true))
      (0 : Fin ((List.replicate C true).length + 1)) (fun _ => C + 1)
    · intro s
      simpa using splitSource_constant C s
    · intro l; simp
  | succ e =>
    apply splitSolve_source C (e + 1) (catalogPolyUnaryTM e C) (.loop (Fin.last e))
      (fun l => catalogPolyCost (l + 1) C (e + 1) + 1)
    · exact splitSource_poly e C
    · intro l
      exact Nat.add_le_add_right (catalogPolyCost_le (l + 1) C (by omega) (e + 1)) 1

/-- The split-search round contracts in the loop's hypothesis form, for any exact unary source
(today's `splitSolve_source`, with the round budget `(A + 5)·(n + 1)^(e + 1)`). -/
private theorem split_hyps (C e : ℕ) (M : FinTM Bool) (start : M.State) (B : ℕ → ℕ)
    (hsource : ∀ s : List Bool, M.tm.runFrom (splitBank M s (some start) []) (B s.length) =
      splitBank M s none (List.replicate (C * (s.length + 1) ^ e) true))
    (hbound : ∀ l, B l ≤ (C + 1 + 5 * e) * (l + 1) ^ e + 1) :
    (∀ w : List Bool, ∃ t ≤ ((C + 1 + 5 * e) * 2 ^ e + 40 + 5) * (w.length + 1) ^ (e + 1),
      (∀ t' < t, ((splitBodyTM M start).tm.runFrom ((splitBodyTM M start).tm.initCfg w)
        t').state ≠ some .anchor) ∧
      (splitBodyTM M start).tm.runFrom ((splitBodyTM M start).tm.initCfg w) t =
        Cfg.ofWords .anchor (stateWord (splitBodyTM M start).k [])) ∧
    (∀ (w s : List Bool), s.length ≤ w.length + 1 →
      ∃ t, 0 < t ∧ t ≤ ((C + 1 + 5 * e) * 2 ^ e + 40 + 5) * (w.length + 1) ^ (e + 1) ∧
        (∀ t', 0 < t' → t' < t →
          ((splitBodyTM M start).tm.runFrom (Cfg.ofWords (input := w) .anchor
            (stateWord (splitBodyTM M start).k s)) t').state ≠ some .anchor) ∧
        if splitAccept C e w s then
          ((splitBodyTM M start).tm.runFrom (Cfg.ofWords (input := w) .anchor
            (stateWord (splitBodyTM M start).k s)) t).state = none ∧
          ((splitBodyTM M start).tm.runFrom (Cfg.ofWords (input := w) .anchor
            (stateWord (splitBodyTM M start).k s)) t).output =
              pairEncode (w.take s.length) (w.drop s.length)
        else
          (splitBodyTM M start).tm.runFrom (Cfg.ofWords (input := w) .anchor
            (stateWord (splitBodyTM M start).k s)) t =
              Cfg.ofWords .anchor (stateWord (splitBodyTM M start).k (splitStep w s))) := by
  refine ⟨fun w => ⟨0, Nat.zero_le _, fun j hj => absurd hj (Nat.not_lt_zero _),
    splitBody_start M start w⟩, fun w s hs => ?_⟩
  obtain ⟨t, htpos, ht, hsafe, hend⟩ := splitBody_round M start w s
    (List.replicate (C * (s.length + 1) ^ e) true) (B s.length) (hsource s)
  refine ⟨t, htpos, (ht.trans (splitBody_envelope C e s.length w.length (B s.length) hs
    (hbound s.length))).trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)), hsafe, ?_⟩
  simpa only [splitAccept, List.length_replicate] using hend

/-- The two exact unary sources of `splitSolveTM` (today's `splitSolve_closed`). -/
private theorem split_sources (C e : ℕ) :
    ∃ (M : FinTM Bool) (start : M.State) (B : ℕ → ℕ),
      splitSolveTM C e = loopHostTM (splitBodyTM M start) lengthBitsTM .anchor true ∧
      (∀ s : List Bool, M.tm.runFrom (splitBank M s (some start) []) (B s.length) =
        splitBank M s none (List.replicate (C * (s.length + 1) ^ e) true)) ∧
      (∀ l, B l ≤ (C + 1 + 5 * e) * (l + 1) ^ e + 1) := by
  cases e with
  | zero =>
    exact ⟨prependTM (List.replicate C true), (0 : Fin ((List.replicate C true).length + 1)),
      fun _ => C + 1, rfl, fun s => by simpa using splitSource_constant C s, fun l => by simp⟩
  | succ e =>
    exact ⟨catalogPolyUnaryTM e C, .loop (Fin.last e),
      fun l => catalogPolyCost (l + 1) C (e + 1) + 1, rfl, splitSource_poly e C,
      fun l => Nat.add_le_add_right (catalogPolyCost_le (l + 1) C (by omega) (e + 1)) 1⟩

/-- The length counter at the split search's round budget. -/
private theorem split_fuel (C e : ℕ) :
    lengthBitsTM.ComputesFunInTime (fun w => Nat.bits (id w.length))
      (fun n => ((C + 1 + 5 * e) * 2 ^ e + 40 + 5) * (n + 1) ^ (e + 1)) := by
  intro w
  refine (lengthBitsTM_computes w).mono ?_
  have hn : w.length + 1 ≤ (w.length + 1) ^ (e + 1) := Nat.le_self_pow (Nat.succ_ne_zero e) _
  exact (Nat.mul_le_mul_left 5 hn).trans (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))

/-- **The padding split search's time**. The split search computes
`w ↦ pairEncode (w.take i) (w.drop i)` for the solution `i` of `i + C·(i + 1)^e = |w|`
(`Turing.solveSplit`), and `[]` if there is none, within
`20·((C + 1 + 5e)·2^e + 46)·(n + 1)^(e + 2)` steps.

**Proof sketch.** Today's `splitSolve_closed`, `splitSolve_source` and `splitSolve_of_body`,
with the existential loop replaced by `loopHostTM_finds`: the body coefficient is
`A = (C + 1 + 5e)·2^e + 40` (`splitBody_envelope`), the counter's `5` enlarges it to the round
budget `T n = (A + 5)·(n + 1)^(e + 1)`, the fuel is `R n = n`, and `splitLoop_bound` turns
`10·(T n + 1)·(n + 2)` into `2·10·(A + 6)·(n + 1)^(e + 2)`; `splitLoop_result` identifies the
first accepting candidate with `solveSplit`. -/
theorem splitSolveTM_computes (C e : ℕ) :
    (splitSolveTM C e).ComputesFunInTime
      (fun w => match solveSplit C e w.length with
        | some i => pairEncode (w.take i) (w.drop i)
        | none => [])
      (fun n => 20 * ((C + 1 + 5 * e) * 2 ^ e + 46) * (n + 1) ^ (e + 2)) := by
  obtain ⟨M, start, B, heq, hsource, hbound⟩ := split_sources C e
  obtain ⟨hstart, hround⟩ := split_hyps C e M start B hsource hbound
  rw [heq]
  have hM := loopHostTM_finds (splitBodyTM M start) lengthBitsTM .anchor
    (fun w s => s.length ≤ w.length + 1) splitStep (splitAccept C e)
    (fun w s => pairEncode (w.take s.length) (w.drop s.length)) (fun _ => [])
    id (fun n => ((C + 1 + 5 * e) * 2 ^ e + 40 + 5) * (n + 1) ^ (e + 1))
    (split_fuel C e) (by intro w; simp) splitStep_inv hstart hround
  intro w
  have hm := hM w
  dsimp only [id_eq] at hm
  have hb : 10 * (((C + 1 + 5 * e) * 2 ^ e + 40 + 5) * (w.length + 1) ^ (e + 1) + 1) *
      (w.length + 2) ≤ 20 * ((C + 1 + 5 * e) * 2 ^ e + 46) * (w.length + 1) ^ (e + 2) :=
    (splitLoop_bound 10 ((C + 1 + 5 * e) * 2 ^ e + 40 + 5) e w.length).trans
      (le_of_eq (by ring))
  convert hm.mono hb using 1
  exact (splitLoop_result C e w).symm

/-- **The padding split search's space**. At every time the split search has visited at most
`23·k·((C + 1 + 5e)·2^e + 46)·(|x| + 1)^(e + 1)` work cells, where `k` is its tape count: one
polynomial degree below its time.

**Proof sketch.** The space half of Catalog's `f2_splitSolve_of_body`, over the named witness:
`loopHostTM_spaceUsed_le_budget` with the round budget `T n = (A + 5)·(n + 1)^(e + 1)` of
`splitSolveTM_computes` gives `23·k·(T |x| + 1) ≤ 23·k·(A + 6)·(|x| + 1)^(e + 1)`. The round
contracts are today's (the Catalog copy `f2_splitBody_round` has the same statement as
`splitBody_round`); the number of rounds does not appear. -/
theorem splitSolveTM_spaceUsed (C e : ℕ) (x : List Bool) (t : ℕ) :
    (splitSolveTM C e).tm.spaceUsed ((splitSolveTM C e).tm.initCfg x) t ≤
      23 * (splitSolveTM C e).k * ((C + 1 + 5 * e) * 2 ^ e + 46) * (x.length + 1) ^ (e + 1) := by
  obtain ⟨M, start, B, heq, hsource, hbound⟩ := split_sources C e
  obtain ⟨hstart, hround⟩ := split_hyps C e M start B hsource hbound
  rw [heq]
  refine (loopHostTM_spaceUsed_le_budget (splitBodyTM M start) lengthBitsTM .anchor
    (fun w s => s.length ≤ w.length + 1) splitStep (splitAccept C e)
    (fun w s => pairEncode (w.take s.length) (w.drop s.length)) true (fun _ => [])
    id (fun n => ((C + 1 + 5 * e) * 2 ^ e + 40 + 5) * (n + 1) ^ (e + 1))
    (split_fuel C e) (by intro w; simp) splitStep_inv hstart hround x t).trans ?_
  have hp : 1 ≤ (x.length + 1) ^ (e + 1) := Nat.one_le_pow _ _ (Nat.succ_pos _)
  generalize (x.length + 1) ^ (e + 1) = P at hp ⊢
  generalize (C + 1 + 5 * e) * 2 ^ e = A
  calc 23 * (loopHostTM (splitBodyTM M start) lengthBitsTM .anchor true).k *
        ((A + 40 + 5) * P + 1)
      ≤ 23 * (loopHostTM (splitBodyTM M start) lengthBitsTM .anchor true).k *
        ((A + 46) * P) := Nat.mul_le_mul_left _ (by
          have : (A + 46) * P = (A + 40 + 5) * P + P := by ring
          omega)
    _ = _ := by ring

/-- **P10, padding split search** (new; the bounded
search both padding constructions perform, realizable as a
`Turing.FinTM.exists_loopFindTM` instance over the polynomial-evaluation
primitive — the decision loop returns only a Boolean and cannot carry the
split). Search for the unique `i ≤ |w|` with `i + C·(i+1)^e = |w|`
(`Turing.solveSplit`); on success emit the threaded split
`pairEncode (w.take i) (w.drop i)`, and on failure `[]` — rejection when
no length-equation solution exists is the audited obligation.

**Construction sketch** (round 2: an `exists_loopFindTM` instance — the
decision loop exposes only a Boolean and cannot carry the payload,
round-1 finding 3; the narrowing from the catalog's supplied-predicate
search to this fixed length-equation search is recorded in
`machine-library-design.md` §9b). Instance data: round state
`s = List.replicate i true`, the candidate in unary;
`Inv w s := s.length ≤ w.length + 1`;
`stepF w s := if s.length ≤ w.length then s ++ [true] else s` (stall past
the end keeps the invariant step-closed); `acceptF w s` holds iff
`s.length + C·(s.length + 1)^e = w.length`, evaluated by the polynomial
loop and a countdown compare;
`out w s := pairEncode (w.take s.length) (w.drop s.length)` — always
nonempty, so success is distinguishable from the `[]` exhaustion; fuel
`R n := n`, so the orbit is exactly the candidates `0, …, n` and
`List.range.find?` returns the least solution, which strict monotonicity
of `i ↦ i + C·(i+1)^e` makes unique — `Turing.solveSplit`'s own
semantics. -/
theorem computesFunInTime_splitSolve (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun w => match solveSplit C e w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => [])
        fun n => c * (n + 1) ^ (e + 2) := by
  exact splitSolve_closed C e

/-- **P11, fixed-width increment** (harvest: the
enumerator batch's `enumCarryTM`/`enumCarry_correct`, proved with cost at
most twice the width plus two). The little-endian fixed-width successor
(`Turing.incFixed`), with `[]` on overflow, is computable in linear time.
The in-place form of the same carry loop is the loop combinator's fuel
counter.

**Construction sketch.** Two passes: the first scan detects overflow (all
trues) — nothing may be emitted while that is unknown; on a live word the
second pass emits falses over the carry prefix, a true at the first false,
and the remainder verbatim. The harvest source's in-place variant costs at
most twice the width plus two. -/
theorem computesFunInTime_incFixed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => (incFixed x).getD []) fun n => c * (n + 1) := by
  exact ⟨incFixedTM, 3, incFixedTM_computes⟩

/-! Emitter implementation. The append-bit and unary-token contracts are
proved below with coefficients one and three. The width-parametric split
contract is proved by the native `emitterP2*` controller.

The `emitterSplit*` layer generalizes the in-file loop closure without any
monotonicity assumption on the width function. The `emitterCompare*` family
is reimplemented in this file from the A-continuation's `e3c*` templates in
`ClassNP/Nondeterminism.lean` at base d7b5b6f94d28df8095165dd4dfe82fd09ba0d414.
Those originals are unchanged and are not cited as imported privates. The
native accepting emitter is `splitEmitTM`/`splitEmit_run`. The controller below
discharges `emitterSplit_of_body`'s literal configuration and strict-interior
anchor contracts. -/

/-- Width-parametric acceptance tests the exact length equation. It makes
no monotonicity assumption on the width function. -/
private def emitterSplitAccept (f : ℕ → ℕ) (w s : List Bool) : Bool :=
  decide (s.length + f s.length = w.length)

/-- The existing unary-candidate orbit tests the very same predicate, in the
same order, as the width-parametric specification. -/
private lemma emitterSplit_find (f : ℕ → ℕ) (w : List Bool) :
    (List.range (w.length + 1)).find?
      (fun i => emitterSplitAccept f w ((splitStep w)^[i] [])) =
        solveSplitWith f w.length := by
  apply catalogFind_congr
  intro i hi
  have hi' : i ≤ w.length := by simpa only [List.mem_range, Nat.lt_succ_iff] using hi
  rw [splitStep_orbit w i (by omega)]
  apply Bool.eq_iff_iff.mpr
  simp only [emitterSplitAccept, List.length_replicate, decide_eq_true_eq, beq_iff_eq]

/-- The first accepting orbit index emits the original input's split; no
accepting index yields exactly the empty word. -/
private lemma emitterSplit_result (f : ℕ → ℕ) (w : List Bool) :
    (match (List.range (w.length + 1)).find?
        (fun i => emitterSplitAccept f w ((splitStep w)^[i] [])) with
      | some i => pairEncode (w.take ((splitStep w)^[i] []).length)
          (w.drop ((splitStep w)^[i] []).length)
      | none => []) =
    (match solveSplitWith f w.length with
      | some i => pairEncode (w.take i) (w.drop i)
      | none => []) := by
  rw [emitterSplit_find]
  cases hs : solveSplitWith f w.length with
  | none => rfl
  | some i =>
    have hi := List.mem_of_find?_eq_some hs
    have hi' : i ≤ w.length := by simpa only [List.mem_range, Nat.lt_succ_iff] using hi
    simp only [splitStep_orbit w i (by omega), List.length_replicate]

/-- A linear body envelope remains linear in the evaluator deadline after
multiplication by the number of candidates, including zero-length inputs. -/
private lemma emitterSplit_loop_bound (c A n t : ℕ) :
    c * (A * (t + n + 2) + 1) * (n + 2) ≤
      (2 * c * (A + 1)) * (n + 1) * (t + n + 2) := by
  have hfirst : A * (t + n + 2) + 1 ≤ (A + 1) * (t + n + 2) := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  calc
    _ ≤ c * ((A + 1) * (t + n + 2)) * (2 * (n + 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left c hfirst) (by omega)
    _ = _ := by ring

/-- A concrete clean body with the indicated linear evaluator envelope closes
the width-parametric split theorem through the proved result-bearing loop.
**Proof sketch.** Enlarge the common body coefficient to cover binary fuel
generation. The existing unary orbit gives every candidate from zero through
the input length in order. The loop's first success has the specified native
payload, while exhaustion emits nothing. The displayed arithmetic absorbs
startup and the extra final candidate factor without changing the argument
at which the evaluator budget is assessed. -/
private lemma emitterSplit_of_body (f TE : ℕ → ℕ) (body : FinTM Bool)
    (anchor : body.State) (A : ℕ)
    (hstart : ∀ w : List Bool, ∃ t ≤ A * (TE (w.length + 1) + w.length + 2),
      (∀ j < t, (body.tm.runFrom (body.tm.initCfg w) j).state ≠ some anchor) ∧
      body.tm.runFrom (body.tm.initCfg w) t = Cfg.ofWords anchor (stateWord body.k []))
    (hround : ∀ (w s : List Bool), s.length ≤ w.length + 1 →
      ∃ t, 0 < t ∧ t ≤ A * (TE (w.length + 1) + w.length + 2) ∧
        (∀ j, 0 < j → j < t →
          (body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) j).state
            ≠ some anchor) ∧
        if emitterSplitAccept f w s then
          (body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t).state = none ∧
          (body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t).output =
            pairEncode (w.take s.length) (w.drop s.length)
        else
          body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t =
            Cfg.ofWords anchor (stateWord body.k (splitStep w s))) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun w => match solveSplitWith f w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => [])
        (fun n => c * (n + 1) * (TE (n + 1) + n + 2)) := by
  obtain ⟨F, a, hF⟩ := computesFunInTime_lengthBits
  have hbody (n : ℕ) : A * (TE (n + 1) + n + 2) ≤
      (A + a) * (TE (n + 1) + n + 2) := Nat.mul_le_mul_right _ (by omega)
  have hF' : F.ComputesFunInTime (fun w => Nat.bits w.length)
      (fun n => (A + a) * (TE (n + 1) + n + 2)) := by
    intro w
    apply (hF w).mono
    exact (Nat.mul_le_mul_left a (by omega : w.length + 1 ≤
      TE (w.length + 1) + w.length + 2)).trans (Nat.mul_le_mul_right _ (by omega))
  obtain ⟨M, c, hM⟩ := exists_loopFindTM body F anchor
    (fun w s => s.length ≤ w.length + 1) splitStep (emitterSplitAccept f)
    (fun w s => pairEncode (w.take s.length) (w.drop s.length)) (fun _ => [])
    id (fun n => (A + a) * (TE (n + 1) + n + 2)) hF'
    (by intro w; simp) splitStep_inv
    (by
      intro w
      obtain ⟨t, ht, hi, hh⟩ := hstart w
      exact ⟨t, ht.trans (hbody w.length), hi, hh⟩)
    (by
      intro w s hs
      obtain ⟨t, hp, ht, hi, hh⟩ := hround w s hs
      exact ⟨t, hp, ht.trans (hbody w.length), hi, hh⟩)
  refine ⟨M, 2 * c * (A + a + 1), fun w => ?_⟩
  have hm := hM w
  dsimp only [id_eq] at hm
  convert hm.mono (emitterSplit_loop_bound c (A + a) w.length (TE (w.length + 1))) using 1
  exact (emitterSplit_result f w).symm

/-- Equality of one-longer prefixes checks the entire old prefix and the next
optional bit. In particular, a missing bit differs from a present false bit. -/
private lemma emitter_take_succ_eq (u v : List Bool) (j : ℕ) :
    u.take (j + 1) = v.take (j + 1) ↔
      u.take j = v.take j ∧ u[j]? = v[j]? := by
  constructor
  · intro h
    constructor
    · have hh := congrArg (List.take j) h
      simpa only [List.take_take, Nat.min_eq_left (by omega : j ≤ j + 1)] using hh
    · have hh := congrArg (fun xs : List Bool => xs[j]?) h
      simpa only [List.getElem?_take, Nat.lt_succ_self, ↓reduceIte] using hh
  · rintro ⟨hpre, hbit⟩
    rw [List.take_succ, List.take_succ, hpre, hbit]

/-- Two read-only word tapes are compared through their common right blank,
then both heads are restored to zero. The returned Boolean is stored in finite
control; the phase never emits. Empty words use the same positive-time path. -/
private def emitterCompareTM : FinTM Bool where
  k := 2
  State := Fin 3 × Bool
  tm := {
    q₀ := (0, true)
    tr := fun q _ work => match q.1.val with
      | 0 =>
        if work 0 = none ∧ work 1 = none then
          ⟨0, fun _ => (none, .neg), none, some (1, q.2)⟩
        else
          ⟨0, fun _ => (none, .pos), none,
            some (0, q.2 && decide (work 0 = work 1))⟩
      | 1 =>
        if work 0 = none ∧ work 1 = none then
          ⟨0, fun _ => (none, .pos), none, some (2, q.2)⟩
        else ⟨0, fun _ => (none, .neg), none, some (1, q.2)⟩
      | _ => controlAction 0 (some (2, q.2)) }

/-- Both comparison heads are aligned; the physical input and its head are
untouched, both word tapes are preserved, and the physical output is empty. -/
private def emitterCompareCfg (w u v : List Bool) (p : Fin (w.length + 2))
    (q : Fin 3) (b : Bool) (h : ℤ) : Cfg 2 Bool emitterCompareTM.State w :=
  ⟨some (q, b), p, (fun i => if i.val = 0 then bufferTape u else bufferTape v), fun _ => h, []⟩

/-- The comparator cannot mistake an interior aligned position for the common
right blank: at least one of the two complete words still has a bit there. -/
private lemma emitter_compare_nonblank (u v : List Bool) (j : ℕ)
    (hj : j < max u.length v.length) : ¬(u[j]? = none ∧ v[j]? = none) := by
  intro h
  have hu := List.getElem?_eq_none_iff.mp h.1
  have hv := List.getElem?_eq_none_iff.mp h.2
  have : max u.length v.length ≤ j := max_le hu hv
  omega

/-- After `j` forward comparisons the register records equality of the whole
length-`j` prefixes, including any unequal-length mismatch.
**Proof sketch.** Induct on the consumed prefix length. Reading both optional bits extends
prefix equality by one and advances both heads together. -/
private lemma emitter_compare_scan (w u v : List Bool) (p : Fin (w.length + 2)) :
    ∀ j, j ≤ max u.length v.length →
      emitterCompareTM.tm.runFrom (emitterCompareCfg w u v p 0 true 0) j =
        emitterCompareCfg w u v p 0 (decide (u.take j = v.take j)) j := by
  intro j
  induction j with
  | zero => intro _; simp [emitterCompareCfg]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hread : ¬(u[j]? = none ∧ v[j]? = none) :=
      emitter_compare_nonblank u v j (by omega)
    have heq : (decide (u.take j = v.take j) && decide (u[j]? = v[j]?)) =
        decide (u.take (j + 1) = v.take (j + 1)) := by
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact (emitter_take_succ_eq u v j).symm
    simp only [MultiTapeTM.step, emitterCompareCfg, emitterCompareTM,
      Cfg.workTapeSymbols, Fin.val_zero, Fin.val_one, Nat.one_ne_zero, ↓reduceIte, bufferTape_nat,
      if_neg hread]
    refine Cfg.ext ?_ (moveInputPos_zero _) rfl ?_ rfl
    · exact congrArg (fun b => some (0, b)) heq
    · funext i; simp [Action.apply]

/-- The common rewind passes all remaining aligned word cells and their left
blank, preserving the comparison register and restoring both heads exactly.
**Proof sketch.** Induct on the aligned distance to the left blank. At least one word
still occupies each interior position; the final positive move restores zero. -/
private lemma emitter_compare_rewind (w u v : List Bool) (p : Fin (w.length + 2))
    (b : Bool) : ∀ j, j ≤ max u.length v.length →
      emitterCompareTM.tm.runFrom (emitterCompareCfg w u v p 1 b ((j : ℤ) - 1)) (j + 1) =
        emitterCompareCfg w u v p 2 b 0 := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [Nat.cast_zero, zero_sub, MultiTapeTM.step,
      emitterCompareCfg, emitterCompareTM, Cfg.workTapeSymbols,
      Fin.val_zero, Fin.val_one, Nat.one_ne_zero, ↓reduceIte, bufferTape_left, and_self, ↓reduceIte]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply]
  | succ j ih =>
    intro hj
    have hread := emitter_compare_nonblank u v j (by omega : j < max u.length v.length)
    have hs : emitterCompareTM.tm.step
        (emitterCompareCfg w u v p 1 b (((j + 1 : ℕ) : ℤ) - 1)) =
          emitterCompareCfg w u v p 1 b ((j : ℤ) - 1) := by
      have hpos : (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) := by omega
      rw [hpos]
      simp only [MultiTapeTM.step, emitterCompareCfg, emitterCompareTM,
        Cfg.workTapeSymbols, Fin.val_zero, Fin.val_one, Nat.one_ne_zero, ↓reduceIte, bufferTape_nat,
        if_neg hread]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Whole-word comparison returns silently in exactly twice the longer word's
length plus two steps, with both tapes and the physical input head unchanged.
**Proof sketch.** The forward invariant compares full prefixes, so at the
longer length its register is literal word equality. The common-right-blank
transition enters the rewind; the rewind restores both heads at the origin. -/
private lemma emitter_compare_run (w u v : List Bool) (p : Fin (w.length + 2)) :
    emitterCompareTM.tm.runFrom (emitterCompareCfg w u v p 0 true 0)
      (2 * (max u.length v.length + 1)) =
        emitterCompareCfg w u v p 2 (decide (u = v)) 0 := by
  let l := max u.length v.length
  have hu : u.length ≤ l := le_max_left _ _
  have hv : v.length ≤ l := le_max_right _ _
  have hscan := emitter_compare_scan w u v p l (le_refl _)
  rw [List.take_of_length_le hu, List.take_of_length_le hv] at hscan
  have hturn : emitterCompareTM.tm.step (emitterCompareCfg w u v p 0 (decide (u = v)) l) =
      emitterCompareCfg w u v p 1 (decide (u = v)) ((l : ℤ) - 1) := by
    simp only [MultiTapeTM.step, emitterCompareCfg, emitterCompareTM,
      Cfg.workTapeSymbols, Fin.val_zero, Fin.val_one, Nat.one_ne_zero, ↓reduceIte, bufferTape_nat,
      List.getElem?_eq_none hu, List.getElem?_eq_none hv, and_self, ↓reduceIte]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply, sub_eq_add_neg]
  have hfirst : emitterCompareTM.tm.runFrom (emitterCompareCfg w u v p 0 true 0) (l + 1) =
      emitterCompareCfg w u v p 1 (decide (u = v)) ((l : ℤ) - 1) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hscan, hturn]
  rw [show 2 * (max u.length v.length + 1) = (l + 1) + (l + 1) by dsimp [l]; omega,
    MultiTapeTM.runFrom_add, hfirst]
  exact emitter_compare_rewind w u v p (decide (u = v)) l (le_refl _)

/-- A phase with an absorbing return state can be cut at its actual first
return while retaining its complete configuration endpoint.
**Proof sketch.** Choose the least return-state visit. Absorption identifies
its configuration with the known bounded endpoint. The bound proves existence
and bounds the first visit; it is never used to dispatch native control. -/
private lemma emitter_first_entry {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (stop : S → Prop) [DecidablePred stop]
    (c d : Cfg k Bool S w) (T : ℕ)
    (hfix : ∀ z : Cfg k Bool S w, (∃ q, z.state = some q ∧ stop q) → tm.step z = z)
    (hd : ∃ q, d.state = some q ∧ stop q) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, (∀ j < t, ¬∃ q, (tm.runFrom c j).state = some q ∧ stop q) ∧
      tm.runFrom c t = d := by
  classical
  have hh : ∃ t, ∃ q, (tm.runFrom c t).state = some q ∧ stop q := ⟨T, by rw [hT]; exact hd⟩
  let t := Nat.find hh
  have ht : t ≤ T := Nat.find_min' hh (by rw [hT]; exact hd)
  have hs : ∃ q, (tm.runFrom c t).state = some q ∧ stop q := Nat.find_spec hh
  refine ⟨t, ht, fun j hj => Nat.find_min hh hj, ?_⟩
  have hconst : tm.runFrom (tm.runFrom c t) (T - t) = tm.runFrom c t :=
    Function.iterate_fixed (hfix _ hs) _
  have he := tm.runFrom_add c t (T - t)
  rw [Nat.add_sub_of_le ht, hT, hconst] at he
  exact he.symm

/-- The silent comparator reaches its exact endpoint on its first visit to
either Boolean return state, after a positive number of steps.
**Proof sketch.** Use the exact bounded comparator run and cut it at the first visit to
either absorbing return state. Absorption identifies the full endpoint;
the initial scan state excludes time zero. -/
private lemma emitter_compare_first (w u v : List Bool) (p : Fin (w.length + 2)) :
    ∃ t, 0 < t ∧ t ≤ 2 * (max u.length v.length + 1) ∧
      (∀ j < t, ∀ b, (emitterCompareTM.tm.runFrom
        (emitterCompareCfg w u v p 0 true 0) j).state ≠ some (2, b)) ∧
      emitterCompareTM.tm.runFrom (emitterCompareCfg w u v p 0 true 0) t =
        emitterCompareCfg w u v p 2 (decide (u = v)) 0 := by
  obtain ⟨t, ht, hfirst, hr⟩ := emitter_first_entry emitterCompareTM.tm
    (fun q : Fin 3 × Bool => q.1 = 2)
    (emitterCompareCfg w u v p 0 true 0) (emitterCompareCfg w u v p 2 (decide (u = v)) 0)
    (2 * (max u.length v.length + 1)) (by
      rintro z ⟨⟨q, b⟩, hz, hq⟩
      change q = 2 at hq
      subst q
      unfold MultiTapeTM.step
      rw [hz]
      change (controlAction 0 (some (2, b))).apply z = z
      rw [controlAction_apply, moveInputPos_zero]
      cases z; simp_all)
    ⟨(2, decide (u = v)), rfl, rfl⟩ (emitter_compare_run w u v p)
  have hpos : 0 < t := by
    by_contra h
    have hz : t = 0 := by omega
    have hh := congrArg Cfg.state hr
    simp [hz, emitterCompareCfg] at hh
    have hv := congrArg (fun q : Fin 3 × Bool => q.1.val) hh
    norm_num at hv
  exact ⟨t, hpos, ht, fun j hj b hb => hfirst j hj ⟨(2, b), hb, rfl⟩, hr⟩

/-- Canonical binary words represent natural numbers injectively. This is
used only to identify an already-completed whole-word comparison. -/
private lemma emitter_bits_injective : Function.Injective Nat.bits := by
  have decode (n : ℕ) : n.bits.foldr Nat.bit 0 = n := by
    induction n using Nat.binaryRec' with
    | zero => simp
    | bit b n hn ih => rw [Nat.bits_append_bit n b hn, List.foldr_cons, ih]
  intro m n h
  have he := congrArg (fun w : List Bool => w.foldr Nat.bit 0) h
  simpa only [decode] using he

/-- Comparing entire canonical binary words is exactly the width equation
on every candidate within the native input. This includes two empty words. -/
private lemma emitter_binary_check (f : ℕ → ℕ) (w s : List Bool)
    (hs : s.length ≤ w.length) :
    (Nat.bits (f s.length) = Nat.bits (w.drop s.length).length) ↔
      s.length + f s.length = w.length := by
  rw [emitter_bits_injective.eq_iff, List.length_drop]
  omega

/-- The evaluator and its captured output are charged at the actual candidate
length before monotonicity enlarges the bound. No preparation-length surrogate
is supplied as the argument of the arbitrary monotone budget. -/
private lemma emitter_width_budget (f : ℕ → ℕ) (E : FinTM Bool)
    (TE : ℕ → ℕ) (hTE : Monotone TE)
    (hE : E.ComputesFunInTime (fun s => Nat.bits (f s.length)) TE)
    (w s : List Bool) (hs : s.length ≤ w.length + 1) :
    E.ComputesInTime s (Nat.bits (f s.length)) (TE s.length) ∧
      (Nat.bits (f s.length)).length ≤ TE s.length ∧ TE s.length ≤ TE (w.length + 1) := by
  have he := hE s
  have hout := ((computesInTime_iff _ _ _ _).mp he).2
  refine ⟨he, ?_, hTE hs⟩
  simpa only [hout] using E.tm.output_length_le s (TE s.length)

/-! **Emitter P2 implementation.** The controller below proves the
width-parametric split contract. Its generic relocation layer is reimplemented
from batch L's `emCall` family in `Build/Loop.lean`, per the private-harvest
policy. It preserves inactive storage and follows observed returns, including
the mandatory first action when entry equals exit. -/









/-- Clear one contiguous administrative word and restore its head. Unlike
source-bank cleanup, this phase may use blanks as word boundaries: the input
is a complete canonical word returned by a clean call. -/
private def emitterP2EraseTM : FinTM Bool where
  k := 1
  State := Fin 3
  tm := {
    q₀ := 0
    tr := fun q _ work => match q.val with
      | 0 => match work 0 with
        | some _ => ⟨0, fun _ => (none, .pos), none, some 0⟩
        | none => ⟨0, fun _ => (none, .neg), none, some 1⟩
      | 1 => match work 0 with
        | some _ => ⟨0, fun _ => (some none, .neg), none, some 1⟩
        | none => ⟨0, fun _ => (none, .pos), none, some 2⟩
      | _ => controlAction 0 (some 2) }

/-- The eraser keeps the physical input at its origin and emits nothing. -/
private def emitterP2EraseCfg (w u : List Bool) (q : Fin 3) (h : ℤ) :
    Cfg 1 Bool (Fin 3) w :=
  ⟨some q, 1, fun _ => bufferTape u, fun _ => h, []⟩

/-- Scan the intact administrative word to its right blank.
**Proof sketch.** Every proper prefix ends at a nonblank cell. The phase
preserves the word and advances its sole head by one. -/
private lemma emitterP2_erase_scan (w u : List Bool) : ∀ j, j ≤ u.length →
    emitterP2EraseTM.tm.runFrom (emitterP2EraseCfg w u 0 0) j =
      emitterP2EraseCfg w u 0 j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    simp only [MultiTapeTM.step, emitterP2EraseCfg, emitterP2EraseTM,
      Cfg.workTapeSymbols, bufferTape_nat, List.getElem?_eq_getElem (by omega : j < u.length)]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply]

/-- Erase right to left, then cross the left blank once to restore zero.
**Proof sketch.** Induct by removing the last bit. Erasing its cell restores
exactly the shorter buffer, including blanks outside it. The empty case
moves from minus one to zero without a write. -/
private lemma emitterP2_erase_back (w u : List Bool) :
    emitterP2EraseTM.tm.runFrom
      (emitterP2EraseCfg w u 1 ((u.length : ℤ) - 1)) (u.length + 1) =
        emitterP2EraseCfg w [] 2 0 := by
  induction u using List.reverseRecOn with
  | nil =>
    simp only [List.length_nil, Nat.cast_zero]
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [MultiTapeTM.step, emitterP2EraseCfg, emitterP2EraseTM,
      Cfg.workTapeSymbols, bufferTape_nil]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply]
  | append_singleton u b ih =>
    have hs : emitterP2EraseTM.tm.step
        (emitterP2EraseCfg w (u ++ [b]) 1 (((u ++ [b]).length : ℤ) - 1)) =
          emitterP2EraseCfg w u 1 ((u.length : ℤ) - 1) := by
      have hp : (((u ++ [b]).length : ℤ) - 1) = (u.length : ℤ) := by simp
      rw [hp]
      simp only [MultiTapeTM.step, emitterP2EraseCfg, emitterP2EraseTM,
        Cfg.workTapeSymbols, bufferTape_nat, List.getElem?_append_right (le_refl _),
        Nat.sub_self, List.getElem?_cons_zero]
      refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
      · funext i; exact catalogBuffer_erase u b
      · funext i; simp [Action.apply, sub_eq_add_neg]
    simp only [List.length_append, List.length_singleton] at hs ⊢
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih

/-- The complete administrative-word erasure costs twice its length plus two.
All cells, the head, physical output, and native input position are restored. -/
private lemma emitterP2_erase_run (w u : List Bool) :
    emitterP2EraseTM.tm.runFrom (emitterP2EraseCfg w u 0 0) (2 * (u.length + 1)) =
      emitterP2EraseCfg w [] 2 0 := by
  have hs := emitterP2_erase_scan w u u.length (le_refl _)
  have ht : emitterP2EraseTM.tm.step (emitterP2EraseCfg w u 0 u.length) =
      emitterP2EraseCfg w u 1 ((u.length : ℤ) - 1) := by
    simp only [MultiTapeTM.step, emitterP2EraseCfg, emitterP2EraseTM,
      Cfg.workTapeSymbols, bufferTape_nat, List.getElem?_length]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply, sub_eq_add_neg]
  have ha : emitterP2EraseTM.tm.runFrom (emitterP2EraseCfg w u 0 0) (u.length + 1) =
      emitterP2EraseCfg w u 1 ((u.length : ℤ) - 1) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hs, ht]
  rw [show 2 * (u.length + 1) = (u.length + 1) + (u.length + 1) by omega,
    MultiTapeTM.runFrom_add, ha]
  exact emitterP2_erase_back w u

/-- Cut the eraser at its observed first return. No length is used as a
native clock, and the return is positive even when the word is empty.
**Proof sketch.** Cut the absorbing eraser exit at its least visit. Absorption preserves the full blank endpoint, and distinct initial/exit controls give positive time. -/
private lemma emitterP2_erase_first (w u : List Bool) :
    ∃ t, 0 < t ∧ t ≤ 2 * (u.length + 1) ∧
      (∀ j < t, (emitterP2EraseTM.tm.runFrom (emitterP2EraseCfg w u 0 0) j).state
        ≠ some (2 : Fin 3)) ∧
      emitterP2EraseTM.tm.runFrom (emitterP2EraseCfg w u 0 0) t =
        emitterP2EraseCfg w [] 2 0 := by
  obtain ⟨t, ht, hf, hr⟩ := emitter_first_entry emitterP2EraseTM.tm
    (fun q : Fin 3 => q = 2) (emitterP2EraseCfg w u 0 0) (emitterP2EraseCfg w [] 2 0)
    (2 * (u.length + 1)) (by
      rintro z ⟨q, hz, rfl⟩
      simp only [MultiTapeTM.step, hz]
      change (controlAction 0 (some (2 : Fin 3))).apply z = z
      rw [controlAction_apply, moveInputPos_zero]
      cases z; simp_all)
    ⟨(2 : Fin 3), rfl, rfl⟩ (emitterP2_erase_run w u)
  refine ⟨t, ?_, ht, fun j hj h => hf j hj ⟨(2 : Fin 3), h, rfl⟩, hr⟩
  by_contra h
  have hz : t = 0 := by omega
  have he := congrArg Cfg.state hr
  simp [hz, emitterP2EraseCfg] at he
/-- Prepare the exact candidate and original native suffix on two fresh word
tapes. The candidate itself is retained, all heads are restored, and a finite
flag records only whether the candidate passed the native right boundary. -/
private def emitterP2PrepareTM : FinTM Bool where
  k := 3
  State := Fin 9 × Bool
  tm := {
    q₀ := (0, false)
    tr := fun q inp work => match q.1.val with
      | 0 => match work 0 with
        | some b => ⟨.pos, fun i =>
            (if i = 1 then some (some b) else none, if i = 2 then 0 else .pos),
            none, some (0, q.2 || inp.isNone)⟩
        | none => controlAction 0 (some (1, q.2))
      | 1 => match inp with
        | some b => ⟨.pos, fun i =>
            (if i = 2 then some (some b) else none, if i = 2 then .pos else 0),
            none, some (1, q.2)⟩
        | none => controlAction 0 (some (2, q.2))
      | 2 => ⟨0, fun i => (none, if i = 2 then 0 else .neg), none, some (3, q.2)⟩
      | 3 => match work 0 with
        | some _ => ⟨0, fun i => (none, if i = 2 then 0 else .neg), none, some (3, q.2)⟩
        | none => ⟨0, fun i => (none, if i = 2 then 0 else .pos), none, some (4, q.2)⟩
      | 4 => ⟨0, fun i => (none, if i = 2 then .neg else 0), none, some (5, q.2)⟩
      | 5 => match work 2 with
        | some _ => ⟨0, fun i => (none, if i = 2 then .neg else 0), none, some (5, q.2)⟩
        | none => ⟨0, fun i => (none, if i = 2 then .pos else 0), none, some (6, q.2)⟩
      | 6 => controlAction .neg (some (7, q.2))
      | 7 => match inp with
        | some _ => controlAction .neg (some (7, q.2))
        | none => controlAction .pos (some (8, q.2))
      | _ => controlAction 0 (some (8, q.2)) }

/-- Preparation frames keep candidate and evaluator-argument heads aligned;
the third tape contains the scanned native suffix. -/
private def emitterP2PrepareCfg (w s u v : List Bool) (q : Fin 9) (over : Bool)
    (p : Fin (w.length + 2)) (a b : ℤ) : Cfg 3 Bool emitterP2PrepareTM.State w :=
  ⟨some (q, over), p,
    (fun i => if i = 0 then bufferTape s else if i = 1 then bufferTape u else bufferTape v),
    (fun i => if i = 2 then b else a), []⟩

/-- The candidate copy uses its literal bits and length. The overflow flag is
set exactly when a nonblank candidate cell faces the native right boundary.
**Proof sketch.** Induct on the candidate prefix. The source candidate never
changes; the second tape appends the same bit; the native head advances with
saturation, and the finite flag updates the strict length comparison. -/
private lemma emitterP2_prepare_candidate (w s : List Bool) : ∀ j, j ≤ s.length →
    emitterP2PrepareTM.tm.runFrom
      (emitterP2PrepareCfg w s [] [] 0 false 1 0 0) j =
        emitterP2PrepareCfg w s (s.take j) [] 0 (decide (w.length < j))
          (splitPos w j) j 0 := by
  intro j
  induction j with
  | zero =>
    intro _
    simp [emitterP2PrepareCfg, splitPos]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    let c := emitterP2PrepareCfg w s (s.take j) [] 0 (decide (w.length < j))
      (splitPos w j) j 0
    have hin := splitPos_read w c j rfl
    have hb : (decide (w.length < j) || c.inputSymbol.isNone) =
        decide (w.length < j + 1) := by
      rw [hin]
      split <;> simp_all <;> omega
    have hlen : (s.take j).length = j := List.length_take_of_le (by omega)
    have hwrite : Function.update (bufferTape (s.take j)) (j : ℤ) (some s[j]) =
        bufferTape (s.take (j + 1)) := by
      rw [List.take_succ, List.getElem?_eq_getElem (by omega : j < s.length)]
      simpa only [Option.toList_some, hlen] using (bufferTape_append (s.take j) s[j]).symm
    change emitterP2PrepareTM.tm.step c = _
    simp only [MultiTapeTM.step, c, emitterP2PrepareCfg, emitterP2PrepareTM,
      Cfg.workTapeSymbols, Fin.reduceEq, ↓reduceIte, bufferTape_nat,
      List.getElem?_eq_getElem (by omega : j < s.length)]
    refine Cfg.ext ?_ (splitPos_succ w j) ?_ ?_ rfl
    · exact congrArg (fun b => some ((0 : Fin 9), b)) hb
    · funext i; fin_cases i <;> simp [Action.apply, emitterP2PrepareCfg, hwrite]
    · funext i; fin_cases i <;> simp [Action.apply, emitterP2PrepareCfg]
/-- Copy the actual native suffix after consuming the candidate length.
**Proof sketch.** At suffix index `j`, the native head reads position
`|s|+j`; the third tape appends exactly that bit. The other tapes are fixed. -/
private lemma emitterP2_prepare_suffix (w s : List Bool) (over : Bool) :
    ∀ j, j ≤ (w.drop s.length).length →
      emitterP2PrepareTM.tm.runFrom
        (emitterP2PrepareCfg w s s [] 1 over (splitPos w s.length) s.length 0) j =
          emitterP2PrepareCfg w s s ((w.drop s.length).take j) 1 over
            (splitPos w (s.length + j)) s.length j := by
  intro j
  induction j with
  | zero => intro _; simp [emitterP2PrepareCfg]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hlt : s.length + j < w.length := by simp only [List.length_drop] at hj; omega
    let v := w.drop s.length
    let c := emitterP2PrepareCfg w s s (v.take j) 1 over
      (splitPos w (s.length + j)) s.length j
    have hin : c.inputSymbol = some v[j] := by
      rw [splitPos_read w c (s.length + j) rfl, dif_pos hlt]
      simp [v, List.getElem_drop]
    have hlen : (v.take j).length = j := List.length_take_of_le (by dsimp [v]; omega)
    have hwrite : Function.update (bufferTape (v.take j)) (j : ℤ) (some v[j]) =
        bufferTape (v.take (j + 1)) := by
      rw [List.take_succ, List.getElem?_eq_getElem (by dsimp [v]; omega : j < v.length)]
      simpa only [Option.toList_some, hlen] using (bufferTape_append (v.take j) v[j]).symm
    change emitterP2PrepareTM.tm.step c = _
    simp only [MultiTapeTM.step, c, emitterP2PrepareCfg]
    change (emitterP2PrepareTM.tm.tr (1, over) c.inputSymbol c.workTapeSymbols).apply c = _
    rw [hin]
    refine Cfg.ext rfl ?_ ?_ ?_ rfl
    · simpa only [Nat.add_assoc] using splitPos_succ w (s.length + j)
    · funext i; fin_cases i <;> simp [emitterP2PrepareTM, Action.apply, c,
        emitterP2PrepareCfg, hwrite] <;> rfl
    · funext i; fin_cases i <;> simp [emitterP2PrepareTM, Action.apply, c,
        emitterP2PrepareCfg]

/-- Rewind the candidate and its copy together without changing either word.
The physical input and prepared suffix remain fixed.
**Proof sketch.** Induct on the distance from the left blank. Each nonblank candidate cell moves both aligned heads left; the blank transition restores both to zero. -/
private lemma emitterP2_prepare_rewind_candidate (w s v : List Bool) (over : Bool)
    (p : Fin (w.length + 2)) (b : ℤ) : ∀ j, j ≤ s.length →
      emitterP2PrepareTM.tm.runFrom
        (emitterP2PrepareCfg w s s v 3 over p ((j : ℤ) - 1) b) (j + 1) =
          emitterP2PrepareCfg w s s v 4 over p 0 b := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [Nat.cast_zero, zero_sub, MultiTapeTM.step, emitterP2PrepareCfg,
      emitterP2PrepareTM, Cfg.workTapeSymbols, Fin.reduceEq, ↓reduceIte, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; fin_cases i <;> simp [Action.apply, emitterP2PrepareCfg]
  | succ j ih =>
    intro hj
    have hs : emitterP2PrepareTM.tm.step
        (emitterP2PrepareCfg w s s v 3 over p (((j + 1 : ℕ) : ℤ) - 1) b) =
          emitterP2PrepareCfg w s s v 3 over p ((j : ℤ) - 1) b := by
      rw [show (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) by omega]
      simp only [MultiTapeTM.step, emitterP2PrepareCfg, emitterP2PrepareTM,
        Cfg.workTapeSymbols, Fin.reduceEq, ↓reduceIte, bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < s.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; fin_cases i <;> simp [Action.apply, emitterP2PrepareCfg, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Rewind the suffix word to zero after candidate restoration.
**Proof sketch.** Induct on the suffix head distance. The word is retained, and one final right move from the left blank restores the origin. -/
private lemma emitterP2_prepare_rewind_suffix (w s v : List Bool) (over : Bool)
    (p : Fin (w.length + 2)) : ∀ j, j ≤ v.length →
      emitterP2PrepareTM.tm.runFrom
        (emitterP2PrepareCfg w s s v 5 over p 0 ((j : ℤ) - 1)) (j + 1) =
          emitterP2PrepareCfg w s s v 6 over p 0 0 := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [Nat.cast_zero, zero_sub, MultiTapeTM.step, emitterP2PrepareCfg,
      emitterP2PrepareTM, Cfg.workTapeSymbols, Fin.reduceEq, ↓reduceIte, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; fin_cases i <;> simp [Action.apply, emitterP2PrepareCfg]
  | succ j ih =>
    intro hj
    have hs : emitterP2PrepareTM.tm.step
        (emitterP2PrepareCfg w s s v 5 over p 0 (((j + 1 : ℕ) : ℤ) - 1)) =
          emitterP2PrepareCfg w s s v 5 over p 0 ((j : ℤ) - 1) := by
      rw [show (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) by omega]
      simp only [MultiTapeTM.step, emitterP2PrepareCfg, emitterP2PrepareTM,
        Cfg.workTapeSymbols, Fin.reduceEq, ↓reduceIte, bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < v.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; fin_cases i <;> simp [Action.apply, emitterP2PrepareCfg, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)
/-- Concatenate exact native phase endpoints without hiding dispatch steps. -/
private lemma emitterP2_join {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) {a b : ℕ} {c d e : Cfg k Bool S w}
    (ha : tm.runFrom c a = d) (hb : tm.runFrom d b = e) :
    tm.runFrom c (a + b) = e := by
  rw [MultiTapeTM.runFrom_add, ha, hb]

/-- The complete native preparation restores every head and presents the
actual candidate and actual original suffix on clean argument tapes.
**Proof sketch.** Copy the candidate, copy the remaining native input, rewind
the two aligned candidate heads, rewind the suffix head, and finally rewind
the native input. Every transition between these phases is charged. -/
private lemma emitterP2_prepare_run (w s : List Bool) :
    ∃ t ≤ 5 * (s.length + w.length + 3),
      emitterP2PrepareTM.tm.runFrom
        (emitterP2PrepareCfg w s [] [] 0 false 1 0 0) t =
          emitterP2PrepareCfg w s s (w.drop s.length) 8 (decide (w.length < s.length)) 1 0 0 := by
  let tm := emitterP2PrepareTM.tm
  let v := w.drop s.length
  let over := decide (w.length < s.length)
  let p := splitPos w (s.length + v.length)
  have hp : p.val = w.length + 1 := by
    dsimp [p, splitPos, v]
    simp only [List.length_drop]
    omega
  have hcopy := emitterP2_prepare_candidate w s s.length (le_refl _)
  simp only [List.take_length] at hcopy
  have h1 : tm.runFrom (emitterP2PrepareCfg w s [] [] 0 false 1 0 0) (s.length + 1) =
      emitterP2PrepareCfg w s s [] 1 over (splitPos w s.length) s.length 0 := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hcopy]
    simp only [tm, MultiTapeTM.step, emitterP2PrepareCfg, emitterP2PrepareTM,
      Cfg.workTapeSymbols, Fin.reduceEq, ↓reduceIte, bufferTape_nat, List.getElem?_length]
    rw [controlAction_apply, moveInputPos_zero]
  have hsuffix := emitterP2_prepare_suffix w s over v.length (le_refl _)
  simp only [v, List.take_length] at hsuffix
  have h2 : tm.runFrom
      (emitterP2PrepareCfg w s s [] 1 over (splitPos w s.length) s.length 0) (v.length + 1) =
        emitterP2PrepareCfg w s s v 2 over p s.length v.length := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hsuffix]
    let c := emitterP2PrepareCfg w s s v 1 over p s.length v.length
    have hin : c.inputSymbol = none := by simp [Cfg.inputSymbol, c, emitterP2PrepareCfg, hp]
    change tm.step c = _
    simp only [MultiTapeTM.step, c, emitterP2PrepareCfg]
    change (emitterP2PrepareTM.tm.tr (1, over) c.inputSymbol c.workTapeSymbols).apply c = _
    rw [hin]
    change (controlAction 0 (some ((2 : Fin 9), over))).apply c = _
    rw [controlAction_apply, moveInputPos_zero]
    rfl
  have h3 : tm.runFrom (emitterP2PrepareCfg w s s v 2 over p s.length v.length)
      (1 + (s.length + 1)) = emitterP2PrepareCfg w s s v 4 over p 0 v.length := by
    have hstep : tm.step (emitterP2PrepareCfg w s s v 2 over p s.length v.length) =
        emitterP2PrepareCfg w s s v 3 over p ((s.length : ℤ) - 1) v.length := by
      simp only [MultiTapeTM.step, emitterP2PrepareCfg, tm, emitterP2PrepareTM]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; fin_cases i <;> simp [Action.apply, sub_eq_add_neg]
    rw [Nat.add_comm 1 _, MultiTapeTM.runFrom_succ_eq_step, hstep]
    exact emitterP2_prepare_rewind_candidate w s v over p v.length s.length (le_refl _)
  have h4 : tm.runFrom (emitterP2PrepareCfg w s s v 4 over p 0 v.length)
      (1 + (v.length + 1)) = emitterP2PrepareCfg w s s v 6 over p 0 0 := by
    have hstep : tm.step (emitterP2PrepareCfg w s s v 4 over p 0 v.length) =
        emitterP2PrepareCfg w s s v 5 over p 0 ((v.length : ℤ) - 1) := by
      simp only [MultiTapeTM.step, emitterP2PrepareCfg, tm, emitterP2PrepareTM]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; fin_cases i <;> simp [Action.apply, sub_eq_add_neg]
    rw [Nat.add_comm 1 _, MultiTapeTM.runFrom_succ_eq_step, hstep]
    exact emitterP2_prepare_rewind_suffix w s v over p v.length (le_refl _)
  obtain ⟨r, hr, h5⟩ := catalogRewind tm ((6 : Fin 9), over) ((7 : Fin 9), over)
    (some ((8 : Fin 9), over)) (fun _ _ => rfl) (fun _ _ => rfl)
    (emitterP2PrepareCfg w s s v 6 over p 0 0) rfl
  have hr' : r ≤ w.length + 3 := by simpa only [emitterP2PrepareCfg, hp] using hr
  have h5' : tm.runFrom (emitterP2PrepareCfg w s s v 6 over p 0 0) r =
      emitterP2PrepareCfg w s s v 8 over 1 0 0 := h5
  refine ⟨s.length + 1 + (v.length + 1) + (1 + (s.length + 1)) +
    (1 + (v.length + 1)) + r, ?_, ?_⟩
  · have hv : v.length ≤ w.length := by dsimp [v]; simp only [List.length_drop]; omega
    omega
  · exact emitterP2_join tm (emitterP2_join tm (emitterP2_join tm
      (emitterP2_join tm h1 h2) h3) h4) h5'

/-- Preparation can be dispatched on its first observed return, with a
positive duration even for empty input and an empty candidate.
**Proof sketch.** Cut the complete preparation run at its first visit to its absorbing return phase. The complete frame is unchanged by later steps, so the first visit has that same frame. -/
private lemma emitterP2_prepare_first (w s : List Bool) :
    ∃ t, 0 < t ∧ t ≤ 5 * (s.length + w.length + 3) ∧
      (∀ j < t, ∀ b, (emitterP2PrepareTM.tm.runFrom
        (emitterP2PrepareCfg w s [] [] 0 false 1 0 0) j).state ≠ some ((8 : Fin 9), b)) ∧
      emitterP2PrepareTM.tm.runFrom (emitterP2PrepareCfg w s [] [] 0 false 1 0 0) t =
        emitterP2PrepareCfg w s s (w.drop s.length) 8 (decide (w.length < s.length)) 1 0 0 := by
  obtain ⟨T, hT, hr⟩ := emitterP2_prepare_run w s
  obtain ⟨t, ht, hf, he⟩ := emitter_first_entry emitterP2PrepareTM.tm
    (fun q : Fin 9 × Bool => q.1 = 8) _ _ T (by
      rintro z ⟨⟨q, b⟩, hz, hq⟩
      change q = 8 at hq
      subst q
      simp only [MultiTapeTM.step, hz]
      change (controlAction 0 (some ((8 : Fin 9), b))).apply z = z
      rw [controlAction_apply, moveInputPos_zero]
      cases z; simp_all)
    ⟨((8 : Fin 9), decide (w.length < s.length)), rfl, rfl⟩ hr
  refine ⟨t, ?_, ht.trans hT, fun j hj b h => hf j hj ⟨((8 : Fin 9), b), h, rfl⟩, he⟩
  by_contra h
  have hz : t = 0 := by omega
  have he' := congrArg Cfg.state he
  simp [hz, emitterP2PrepareCfg] at he'
  have hv := congrArg (fun q : Fin 9 × Bool => q.1.val) he'.symm
  norm_num at hv
/-- A tape-embedded phase reaches its source endpoint and avoids the outer
anchor throughout the trace.
**Proof sketch.** R1 identifies each embedded prefix. The public injective
state-transport theorem applies guarded agreement on the host carrier, and
the range of the state embedding excludes the anchor. -/
private lemma emitterP2_phase {k l : ℕ} {S H : Type} {x : List Bool}
    (src : MultiTapeTM k Bool S) (host : MultiTapeTM l Bool H)
    (index : Fin k ↪ Fin l) (emb : S ↪ H) (anchor : H)
    (haway : ∀ q, emb q ≠ anchor) (good : S → Prop)
    (hagree : ∀ q, good q → ∀ inp work,
      host.tr (emb q) inp work = ((embedEmitTM index src).tr q inp work).mapState emb)
    (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ)
    (c d : Cfg k Bool S x) (t : ℕ)
    (hguard : ∀ j < t, ∀ q, (src.runFrom c j).state = some q → good q)
    (hr : src.runFrom c t = d) :
    host.runFrom ((embedEmitCfg index tapes heads [] c).mapState emb) t =
        (embedEmitCfg index tapes heads [] d).mapState emb ∧
      splitSafe host anchor ((embedEmitCfg index tapes heads [] c).mapState emb) t := by
  have trace (j : ℕ) (hj : j ≤ t) :=
    MultiTapeTM.runFrom_mapState_of_agreeOn (embedEmitTM index src) host emb good hagree
      (embedEmitCfg index tapes heads [] c) j (by
        intro u hu q hq
        rw [embedEmitTM_runFrom] at hq
        exact hguard u (lt_of_lt_of_le hu hj) q hq)
  simp only [embedEmitTM_runFrom] at trace
  constructor
  · simpa only [hr] using trace t le_rfl
  · intro j hj
    rw [trace j hj]
    change (src.runFrom c j).state.map emb ≠ some anchor
    intro he
    obtain ⟨q, _, hq⟩ := Option.map_eq_some_iff.mp he
    exact haway q hq

/-- A clean call executes its first action at a separate entry control,
including when the source entry equals its exit.
**Proof sketch.** R1 at time one and state-map compatibility identify the
mandatory first action. Transfer the remaining source prefix as one phase;
only positive source times are then tested by the exit guard. -/
private lemma emitterP2_call_phase {k l : ℕ} {S H : Type} {x : List Bool}
    (src : MultiTapeTM k Bool S) (host : MultiTapeTM l Bool H)
    (index : Fin k ↪ Fin l) (emb : S ↪ H)
    (enter anchor : H) (henter : enter ≠ anchor) (haway : ∀ q, emb q ≠ anchor)
    (entry exit : S)
    (hstart : ∀ inp work, host.tr enter inp work =
      ((embedEmitTM index src).tr entry inp work).mapState emb)
    (hagree : ∀ q, q ≠ exit → ∀ inp work,
      host.tr (emb q) inp work = ((embedEmitTM index src).tr q inp work).mapState emb)
    (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ)
    (c d : Cfg k Bool S x) (hc : c.state = some entry) (t : ℕ) (ht : 0 < t)
    (hguard : ∀ j, 0 < j → j < t → (src.runFrom c j).state ≠ some exit)
    (hr : src.runFrom c t = d) :
    let z := {(embedEmitCfg index tapes heads [] c).mapState emb with state := some enter}
    host.runFrom z t = (embedEmitCfg index tapes heads [] d).mapState emb ∧
      splitSafe host anchor z t := by
  cases t with
  | zero => omega
  | succ t =>
    let ec := embedEmitCfg index tapes heads [] c
    let z := {ec.mapState emb with state := some enter}
    have first : host.runFrom z 1 = (embedEmitCfg index tapes heads [] (src.runFrom c 1)).mapState emb := by
      change host.step z = (embedEmitCfg index tapes heads [] (src.step c)).mapState emb
      have r1 := congrArg (Cfg.mapState emb) (embedEmitTM_runFrom index src tapes heads [] c 1)
      change ((embedEmitTM index src).step ec).mapState emb =
        (embedEmitCfg index tapes heads [] (src.step c)).mapState emb at r1
      rw [← r1]
      have control : ec.state = some entry := hc
      simp only [MultiTapeTM.step, z, control, hstart]
      exact Cfg.mapState_apply emb _ ec
    obtain ⟨endpoint, safe⟩ := emitterP2_phase src host index emb anchor haway
      (fun q => q ≠ exit) hagree tapes heads (src.runFrom c 1) d t
      (by
        intro j hj q hq he
        apply hguard (1 + j) (by omega) (by omega)
        rw [MultiTapeTM.runFrom_add, hq, he])
      (by simpa only [← MultiTapeTM.runFrom_add, Nat.add_comm 1] using hr)
    constructor
    · change host.runFrom z (t + 1) = _
      rw [Nat.add_comm t 1, MultiTapeTM.runFrom_add, first]
      exact endpoint
    · intro j hj
      cases j with
      | zero => exact fun he => henter (Option.some.inj he)
      | succ j =>
        rw [Nat.add_comm j 1, MultiTapeTM.runFrom_add, first]
        exact safe j (by omega)

/-- Layout: the preserved candidate, the complete width-call bank, then the
complete suffix-length-call bank. Only each bank's first tape carries data
at a seam; all other work tapes are blank. -/
private def emitterP2Words (k l : ℕ) (s u v : List Bool) : Fin (k + l + 1) → List Bool :=
  Fin.cases s (Fin.addCases (stateWord k u) (stateWord l v))

/-- Select the complete left call bank after the candidate tape. -/
private def emitterP2LeftIndex (k l : ℕ) : Fin k ↪ Fin (k + l + 1) :=
  (Fin.castAddEmb l).trans (Fin.succEmb (k + l))

/-- Select the complete right call bank after the candidate tape. -/
private def emitterP2RightIndex (k l : ℕ) : Fin l ↪ Fin (k + l + 1) :=
  (Fin.natAddEmb k).trans (Fin.succEmb (k + l))

/-- Selected source cells and the unselected ambient frame determine the
entire embedded configuration.
**Proof sketch.** Use the two selected-tape exports on the image and the R1
frame contract at time zero off the image. State, input and output are the
remaining three configuration fields. -/
private lemma emitterP2_frame {k l : ℕ} {S H : Type} {x : List Bool}
    (q : S) (index : Fin k ↪ Fin l) (emb : S → H)
    (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ)
    (c : Cfg k Bool S x) (d : Cfg l Bool H x)
    (hs : c.state.map emb = d.state) (hi : c.inputPos = d.inputPos)
    (ho : c.output = d.output)
    (selected : ∀ i, c.workTapes i = d.workTapes (index i) ∧
      c.workTapePos i = d.workTapePos (index i))
    (frame : ∀ j, j ∉ Set.range index → tapes j = d.workTapes j ∧ heads j = d.workTapePos j) :
    (embedEmitCfg index tapes heads [] c).mapState emb = d := by
  have fields (j : Fin l) :
      (embedEmitCfg index tapes heads [] c).workTapes j = d.workTapes j ∧
      (embedEmitCfg index tapes heads [] c).workTapePos j = d.workTapePos j := by
    by_cases hj : j ∈ Set.range index
    · obtain ⟨i, rfl⟩ := hj
      simpa only [embedEmitCfg_selected_tape, embedEmitCfg_selected_pos] using selected i
    · obtain ⟨ht, hp⟩ := (embedEmitTM_frame index ⟨q, fun _ _ _ => controlAction 0 none⟩ tapes heads [] c 0).1 j hj
      exact ⟨ht.trans (frame j hj).1, hp.trans (frame j hj).2⟩
  exact Cfg.ext hs hi (funext fun j => (fields j).1) (funext fun j => (fields j).2) ho

/-- The left bank transport restores a complete canonical host seam.
**Proof sketch.** The selected-tape exports give the active bank. The R1
frame export preserves the candidate and the other bank. -/
private lemma emitterP2_left_frame {S H : Type} (k l : ℕ) (emb : S → H)
    (w s u v : List Bool) (q : S) :
    (embedEmitCfg (emitterP2LeftIndex k l)
      (fun i => bufferTape (emitterP2Words k l s [] v i)) (fun _ => 0) []
      (Cfg.ofWords (input := w) q (stateWord k u))).mapState emb =
        Cfg.ofWords (emb q) (emitterP2Words k l s u v) := by
  apply emitterP2_frame q <;> try rfl
  · intro i
    simp [emitterP2LeftIndex, emitterP2Words, Cfg.ofWords]
  · intro j hj
    refine Fin.cases ?_ (fun a => ?_) j hj
    · intro _; simp [emitterP2Words, Cfg.ofWords]
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) a
      · intro h; exact False.elim (h ⟨i, rfl⟩)
      · intro _; simp [emitterP2Words, Cfg.ofWords]

/-- The right bank transport restores a complete canonical host seam.
**Proof sketch.** The selected-tape exports give the active bank. The R1
frame export preserves the candidate and the other bank. -/
private lemma emitterP2_right_frame {S H : Type} (k l : ℕ) (emb : S → H)
    (w s u v : List Bool) (q : S) :
    (embedEmitCfg (emitterP2RightIndex k l)
      (fun i => bufferTape (emitterP2Words k l s u [] i)) (fun _ => 0) []
      (Cfg.ofWords (input := w) q (stateWord l v))).mapState emb =
        Cfg.ofWords (emb q) (emitterP2Words k l s u v) := by
  apply emitterP2_frame q <;> try rfl
  · intro i
    simp [emitterP2RightIndex, emitterP2Words, Cfg.ofWords]
  · intro j hj
    refine Fin.cases ?_ (fun a => ?_) j hj
    · intro _; simp [emitterP2Words, Cfg.ofWords]
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) a
      · intro _; simp [emitterP2Words, Cfg.ofWords]
      · intro h; exact False.elim (h ⟨i, rfl⟩)

/-- With both argument words erased, the complete host seam is exactly the
loop's canonical state-word seam, including every inactive tape. -/
private lemma emitterP2_words_clean (k l : ℕ) (s : List Bool) :
    emitterP2Words k l s [] [] = stateWord (k + l + 1) s := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [emitterP2Words, stateWord]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      simp [emitterP2Words, stateWord]
/-- A singleton source occupies exactly the specified physical tape. -/
private def emitterP2OneIndex {l : ℕ} (slot : Fin l) : Fin 1 ↪ Fin l where
  toFun _ := slot
  inj' := fun _ _ _ => Subsingleton.elim _ _

/-- A singleton transport changes precisely one host word. -/
private lemma emitterP2_one_frame {l : ℕ} {S H : Type} (slot : Fin l) (emb : S → H)
    (words : Fin l → List Bool) (w u : List Bool) (q : S) :
    (embedEmitCfg (emitterP2OneIndex slot) (fun i => bufferTape (words i)) (fun _ => 0) []
      (Cfg.ofWords (input := w) q (fun _ : Fin 1 => u))).mapState emb =
        Cfg.ofWords (emb q) (Function.update words slot u) := by
  apply emitterP2_frame q <;> try rfl
  · intro i; simp [emitterP2OneIndex, Cfg.ofWords]
  · intro j hj
    have hne : j ≠ slot := fun h => hj ⟨0, h.symm⟩
    simp [Cfg.ofWords, Function.update_of_ne hne]

/-- Inject the 3 administrative tapes into their distinct physical slots. -/
private def emitterP2SmallIndex (k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    Fin 3 ↪ Fin (k + l + 1) where
  toFun i := if i = 0 then 0 else if i = 1 then emitterP2LeftIndex k l ⟨0, hk⟩
    else emitterP2RightIndex k l ⟨0, hl⟩
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> try rfl
    all_goals have hv := congrArg Fin.val h
    all_goals simp [emitterP2LeftIndex, emitterP2RightIndex] at hv <;> omega

/-- The administrative transport is the complete three-word host seam.
**Proof sketch.** The selected slots carry the source words. Every other
slot is an unchanged candidate or a blank scratch tape, by the R1 frame. -/
private lemma emitterP2_small_frame {H : Type} (k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    (emb : Fin 9 × Bool → H) (w s u v : List Bool) (q : Fin 9) (over : Bool) :
    (embedEmitCfg (emitterP2SmallIndex k l hk hl) (fun _ _ => none) (fun _ => 0) []
      (emitterP2PrepareCfg w s u v q over 1 0 0)).mapState emb =
        Cfg.ofWords (emb (q, over)) (emitterP2Words k l s u v) := by
  apply emitterP2_frame (q, over) <;> try rfl
  · intro i
    fin_cases i <;> simp [emitterP2SmallIndex, emitterP2LeftIndex, emitterP2RightIndex,
      emitterP2Words, emitterP2PrepareCfg, Cfg.ofWords, stateWord, Fin.addCases, hk]
  · intro j hj
    refine Fin.cases ?_ (fun a => ?_) j hj
    · intro h; exact False.elim (h ⟨0, rfl⟩)
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) a
      · intro h
        have hn : i.val ≠ 0 := by
          intro he
          have hi : i = ⟨0, hk⟩ := Fin.ext he
          subst i
          exact h ⟨1, rfl⟩
        simp [emitterP2Words, Cfg.ofWords, stateWord, hn, bufferTape_nil]
      · intro h
        have hn : i.val ≠ 0 := by
          intro he
          have hi : i = ⟨0, hl⟩ := Fin.ext he
          subst i
          exact h ⟨2, rfl⟩
        simp [emitterP2Words, Cfg.ofWords, stateWord, hn, bufferTape_nil]

/-- Inject the 2 administrative tapes into their distinct physical slots. -/
private def emitterP2PairIndex (k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    Fin 2 ↪ Fin (k + l + 1) where
  toFun i := if i = 0 then emitterP2LeftIndex k l ⟨0, hk⟩
    else emitterP2RightIndex k l ⟨0, hl⟩
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> try rfl
    all_goals have hv := congrArg Fin.val h
    all_goals simp [emitterP2LeftIndex, emitterP2RightIndex] at hv <;> omega

/-- The administrative transport is the complete three-word host seam.
**Proof sketch.** The selected slots carry the source words. Every other
slot is an unchanged candidate or a blank scratch tape, by the R1 frame. -/
private lemma emitterP2_pair_frame {H : Type} (k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    (emb : Fin 3 × Bool → H) (w s u v : List Bool) (q : Fin 3) (b : Bool) :
    (embedEmitCfg (emitterP2PairIndex k l hk hl) (fun i => bufferTape (emitterP2Words k l s [] [] i)) (fun _ => 0) []
      (emitterCompareCfg w u v 1 q b 0)).mapState emb =
        Cfg.ofWords (emb (q, b)) (emitterP2Words k l s u v) := by
  apply emitterP2_frame (q, b) <;> try rfl
  · intro i
    fin_cases i <;> simp [emitterP2PairIndex, emitterP2LeftIndex, emitterP2RightIndex,
      emitterP2Words, emitterCompareCfg, Cfg.ofWords, stateWord, Fin.addCases, hk]
  · intro j hj
    refine Fin.cases ?_ (fun a => ?_) j hj
    · intro _; simp [emitterP2Words, Cfg.ofWords]
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) a
      · intro h
        have hn : i.val ≠ 0 := by
          intro he
          have hi : i = ⟨0, hk⟩ := Fin.ext he
          subst i
          exact h ⟨0, rfl⟩
        simp [emitterP2Words, Cfg.ofWords, stateWord, hn, bufferTape_nil]
      · intro h
        have hn : i.val ≠ 0 := by
          intro he
          have hi : i = ⟨0, hl⟩ := Fin.ext he
          subst i
          exact h ⟨1, rfl⟩
        simp [emitterP2Words, Cfg.ofWords, stateWord, hn, bufferTape_nil]

/-- Updating the first width-bank word leaves the entire other layout intact.
**Proof sketch.** Split the host index into its three blocks. Only the first width-bank index equals the update address; every other index is unchanged. -/
private lemma emitterP2_update_left (k l : ℕ) (hk : 0 < k) (s u v a : List Bool) :
    Function.update (emitterP2Words k l s u v) (emitterP2LeftIndex k l ⟨0, hk⟩) a =
      emitterP2Words k l s a v := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [Function.update, emitterP2LeftIndex, emitterP2Words]
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · by_cases hj : j.val = 0
      · have he : j = ⟨0, hk⟩ := Fin.ext hj
        subst j; simp [emitterP2LeftIndex, emitterP2Words, stateWord, Fin.addCases, hk]
      · have he : (Fin.castAdd l j).succ ≠ emitterP2LeftIndex k l ⟨0, hk⟩ := by
          intro h; apply hj; have hv := congrArg Fin.val h; simpa [emitterP2LeftIndex] using hv
        rw [Function.update_of_ne he]
        simp [emitterP2Words, stateWord, hj]
    · have he : (Fin.natAdd k j).succ ≠ emitterP2LeftIndex k l ⟨0, hk⟩ := by
        intro h; have hv := congrArg Fin.val h; simp [emitterP2LeftIndex, emitterP2RightIndex] at hv; omega
      rw [Function.update_of_ne he]
      simp [emitterP2Words]

/-- Updating the first length-bank word preserves the candidate and width.
**Proof sketch.** Split the host index into its three blocks. Only the first length-bank index equals the update address; every other index is unchanged. -/
private lemma emitterP2_update_right (k l : ℕ) (hl : 0 < l) (s u v a : List Bool) :
    Function.update (emitterP2Words k l s u v) (emitterP2RightIndex k l ⟨0, hl⟩) a =
      emitterP2Words k l s u a := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [Function.update, emitterP2RightIndex, emitterP2Words]
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have he : (Fin.castAdd l j).succ ≠ emitterP2RightIndex k l ⟨0, hl⟩ := by
        intro h; have hv := congrArg Fin.val h; simp [emitterP2LeftIndex, emitterP2RightIndex] at hv; omega
      rw [Function.update_of_ne he]
      simp [emitterP2Words]
    · by_cases hj : j.val = 0
      · have he : j = ⟨0, hl⟩ := Fin.ext hj
        subst j; simp [emitterP2RightIndex, emitterP2Words, stateWord, Fin.addCases]
      · have he : (Fin.natAdd k j).succ ≠ emitterP2RightIndex k l ⟨0, hl⟩ := by
          intro h; have hv := congrArg Fin.val h; simp [emitterP2LeftIndex, emitterP2RightIndex] at hv; omega
        rw [Function.update_of_ne he]
        simp [emitterP2Words, stateWord, hj]

/-- Updating the preserved candidate changes exactly the loop state word. -/
private lemma emitterP2_update_candidate (k l : ℕ) (s u v a : List Bool) :
    Function.update (emitterP2Words k l s u v) 0 a = emitterP2Words k l a u v := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [emitterP2Words, Function.update]
/-- Distinct controller phases keep all proper round interiors away from the
loop anchor. Module-start states enforce the first-step release discipline. -/
private inductive EmitterP2State (S T : Type) where
  | anchor
  | prepare (q : Fin 9 × Bool)
  | widthStart
  | width (q : S)
  | lengthStart
  | length (q : T)
  | compare (q : Fin 3 × Bool)
  | eraseLeft (ok : Bool) (q : Fin 3)
  | eraseRight (ok : Bool) (q : Fin 3)
  | advance (q : Fin 5 × Bool)
  | emit (q : Fin 4)

private instance emitterP2StateFintype (S T : Type) [Fintype S] [Fintype T] :
    Fintype (EmitterP2State S T) := derive_fintype% _

/-- Controller equality compares only payloads of equal finite phases. -/
private instance emitterP2StateDecidableEq (S T : Type) [DecidableEq S] [DecidableEq T] :
    DecidableEq (EmitterP2State S T) := by
  intro a b
  cases a <;> cases b
  all_goals try (solve | apply isFalse; intro h; cases h)
  · exact isTrue rfl
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (EmitterP2State.prepare.injEq _ _)))
  · exact isTrue rfl
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (EmitterP2State.width.injEq _ _)))
  · exact isTrue rfl
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (EmitterP2State.length.injEq _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (EmitterP2State.compare.injEq _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (EmitterP2State.eraseLeft.injEq _ _ _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (EmitterP2State.eraseRight.injEq _ _ _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (EmitterP2State.advance.injEq _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (EmitterP2State.emit.injEq _ _)))

/-- Native split-search controller. Clean-call modules consume the prepared
candidate and suffix; comparison is whole-word; both result words are erased
before acceptance or rejection. The native input is never overwritten and
supplies every payload bit. A past-end preparation bypasses both evaluators.
No time bound or width function appears in the transition table. -/
private def emitterP2BodyTM (C D : FinTM Bool) (hk : 0 < C.k) (hl : 0 < D.k)
    (ce cx : C.State) (de dx : D.State) : FinTM Bool where
  k := C.k + D.k + 1
  State := EmitterP2State C.State D.State
  tm := {
    q₀ := .anchor
    tr := fun q inp work => match q with
      | .anchor => controlAction 0 (some (.prepare (0, false)))
      | .prepare p =>
        if p.1 = 8 then controlAction 0 (some (if p.2 then .eraseLeft false 0 else .widthStart))
        else ((embedEmitTM (emitterP2SmallIndex C.k D.k hk hl) emitterP2PrepareTM.tm).tr p inp work).mapState .prepare
      | .widthStart => ((embedEmitTM (emitterP2LeftIndex C.k D.k) C.tm).tr ce inp work).mapState .width
      | .width p =>
        if p = cx then controlAction 0 (some .lengthStart)
        else ((embedEmitTM (emitterP2LeftIndex C.k D.k) C.tm).tr p inp work).mapState .width
      | .lengthStart => ((embedEmitTM (emitterP2RightIndex C.k D.k) D.tm).tr de inp work).mapState .length
      | .length p =>
        if p = dx then controlAction 0 (some (.compare (0, true)))
        else ((embedEmitTM (emitterP2RightIndex C.k D.k) D.tm).tr p inp work).mapState .length
      | .compare p =>
        if p.1 = 2 then controlAction 0 (some (.eraseLeft p.2 0))
        else ((embedEmitTM (emitterP2PairIndex C.k D.k hk hl) emitterCompareTM.tm).tr p inp work).mapState .compare
      | .eraseLeft ok p =>
        if p = 2 then controlAction 0 (some (.eraseRight ok 0))
        else ((embedEmitTM (emitterP2OneIndex (emitterP2LeftIndex C.k D.k ⟨0, hk⟩))
          emitterP2EraseTM.tm).tr p inp work).mapState (.eraseLeft ok)
      | .eraseRight ok p =>
        if p = 2 then controlAction 0 (some (if ok then .emit 0 else .advance (0, false)))
        else ((embedEmitTM (emitterP2OneIndex (emitterP2RightIndex C.k D.k ⟨0, hl⟩))
          emitterP2EraseTM.tm).tr p inp work).mapState (.eraseRight ok)
      | .advance p =>
        if p = (4, false) then controlAction 0 (some .anchor)
        else ((embedEmitTM (emitterP2OneIndex (0 : Fin (C.k + D.k + 1)))
          (splitRestoreTM 0).tm).tr p inp work).mapState .advance
      | .emit p => ((embedEmitTM (emitterP2OneIndex (0 : Fin (C.k + D.k + 1)))
          (splitEmitTM 0).tm).tr p inp work).mapState .emit }

/-- **The width-parametric split search**. The find-mode loop host, fuelled by the binary length
counter, over the native split body that, per candidate `i` in unary, evaluates the width machine
`E` on the candidate and the length counter on the suffix through two install-mode clean calls,
compares the two binary words, and either emits the split or advances. The width function itself
does not occur in the machine. -/
def splitSolveWithTM (E : FinTM Bool) : FinTM Bool :=
  loopHostTM
    (emitterP2BodyTM (callTM E false) (callTM lengthBitsTM false) (callTM_k_pos E false)
      (callTM_k_pos lengthBitsTM false) (callEntry E false) (callExit E false)
      (callEntry lengthBitsTM false) (callExit lengthBitsTM false))
    lengthBitsTM .anchor true

/-- Genuine startup is already the canonical empty-candidate anchor. -/
private lemma emitterP2_body_start (C D : FinTM Bool) (hk : 0 < C.k) (hl : 0 < D.k)
    (ce cx : C.State) (de dx : D.State) (w : List Bool) :
    (emitterP2BodyTM C D hk hl ce cx de dx).tm.initCfg w =
      Cfg.ofWords .anchor (stateWord (C.k + D.k + 1) []) := by
  rw [initCfg_ofWords]
  change Cfg.ofWords (input := w) (EmitterP2State.anchor (S := C.State) (T := D.State))
    (fun _ : Fin (C.k + D.k + 1) => []) = _
  congr 1
  funext i; simp [stateWord]

/-- A silent controller dispatch preserves every component of a canonical
word seam and changes only control. -/
private lemma emitterP2_control {k : ℕ} {S : Type} (tm : MultiTapeTM k Bool S)
    (q r : S) (h : ∀ inp work, tm.tr q inp work = controlAction 0 (some r))
    (w : List Bool) (words : Fin k → List Bool) :
    tm.step (Cfg.ofWords (input := w) q words) = Cfg.ofWords r words := by
  simp only [MultiTapeTM.step, Cfg.ofWords, h]
  rw [controlAction_apply, moveInputPos_zero]
/-- Preparation embeds on exactly the three administrative tapes.
**Proof sketch.** Relocate the first-return preparation trace using the three-slot inverse law. The initial and final frame identities give literal host seams; disjoint controls give anchor exclusion. -/
private lemma emitterP2_body_prepare (C D : FinTM Bool) (hk : 0 < C.k) (hl : 0 < D.k)
    (ce cx : C.State) (de dx : D.State) (w s : List Bool) :
    let B := emitterP2BodyTM C D hk hl ce cx de dx
    ∃ t ≤ 5 * (s.length + w.length + 3),
      B.tm.runFrom (Cfg.ofWords (input := w) (.prepare (0, false))
        (emitterP2Words C.k D.k s [] [])) t =
        Cfg.ofWords (.prepare (8, decide (w.length < s.length)))
          (emitterP2Words C.k D.k s s (w.drop s.length)) ∧
      splitSafe B.tm .anchor (Cfg.ofWords (input := w) (.prepare (0, false))
        (emitterP2Words C.k D.k s [] [])) t := by
  dsimp only
  obtain ⟨t, _, ht, hf, hr⟩ := emitterP2_prepare_first w s
  have h := emitterP2_phase emitterP2PrepareTM.tm (emitterP2BodyTM C D hk hl ce cx de dx).tm
    (emitterP2SmallIndex C.k D.k hk hl)
    ⟨EmitterP2State.prepare, by intro a b h; exact EmitterP2State.prepare.inj h⟩ .anchor
    (by intro q; simp) (fun q : Fin 9 × Bool => q.1 ≠ 8)
    (fun _ hq _ _ => if_neg hq)
    (fun _ _ => none) (fun _ => 0)
    (emitterP2PrepareCfg w s [] [] 0 false 1 0 0)
    (emitterP2PrepareCfg w s s (w.drop s.length) 8 (decide (w.length < s.length)) 1 0 0) t
    (by intro j hj q hq he; rcases q with ⟨q, b⟩; dsimp at he; subst q; exact hf j hj b hq) hr
  erw [emitterP2_small_frame _ _ hk hl, emitterP2_small_frame _ _ hk hl] at h
  exact ⟨t, ht, h⟩

/-- The width call consumes exactly its candidate copy while retaining the
original candidate and prepared native suffix in the other blocks.
**Proof sketch.** Apply the first-action clean-call embedding to the width bank. Both endpoint frame identities preserve the surrounding candidate and suffix and restore every inactive cell and head. -/
private lemma emitterP2_body_width (C D : FinTM Bool) (hk : 0 < C.k) (hl : 0 < D.k)
    (ce cx : C.State) (de dx : D.State) (w s u v : List Bool) (t : ℕ) (ht : 0 < t)
    (hf : ∀ j, 0 < j → j < t → (C.tm.runFrom
      (Cfg.ofWords (input := w) ce (stateWord C.k s)) j).state ≠ some cx)
    (hr : C.tm.runFrom (Cfg.ofWords (input := w) ce (stateWord C.k s)) t =
      Cfg.ofWords cx (stateWord C.k u)) :
    let B := emitterP2BodyTM C D hk hl ce cx de dx
    B.tm.runFrom (Cfg.ofWords (input := w) .widthStart (emitterP2Words C.k D.k s s v)) t =
        Cfg.ofWords (.width cx) (emitterP2Words C.k D.k s u v) ∧
      splitSafe B.tm .anchor
        (Cfg.ofWords (input := w) .widthStart (emitterP2Words C.k D.k s s v)) t := by
  dsimp only
  have h := emitterP2_call_phase C.tm (emitterP2BodyTM C D hk hl ce cx de dx).tm
    (emitterP2LeftIndex C.k D.k)
    ⟨EmitterP2State.width, by intro a b h; exact EmitterP2State.width.inj h⟩ .widthStart .anchor
    (by simp) (by intro q; simp) ce cx (fun _ _ => rfl)
    (fun _ hq _ _ => if_neg hq)
    (fun i => bufferTape (emitterP2Words C.k D.k s [] v i)) (fun _ => 0)
    (Cfg.ofWords ce (stateWord C.k s)) (Cfg.ofWords cx (stateWord C.k u)) rfl t ht hf hr
  dsimp only at h
  erw [emitterP2_left_frame, emitterP2_left_frame] at h
  exact h

/-- The length call consumes the actual prepared suffix; its return preserves
the original candidate and the already installed width word.
**Proof sketch.** Apply the first-action clean-call embedding to the length bank, preserving the width result and candidate. Its canonical endpoint supplies every cell and head needed by comparison. -/
private lemma emitterP2_body_length (C D : FinTM Bool) (hk : 0 < C.k) (hl : 0 < D.k)
    (ce cx : C.State) (de dx : D.State) (w s u v z : List Bool) (t : ℕ) (ht : 0 < t)
    (hf : ∀ j, 0 < j → j < t → (D.tm.runFrom
      (Cfg.ofWords (input := w) de (stateWord D.k v)) j).state ≠ some dx)
    (hr : D.tm.runFrom (Cfg.ofWords (input := w) de (stateWord D.k v)) t =
      Cfg.ofWords dx (stateWord D.k z)) :
    let B := emitterP2BodyTM C D hk hl ce cx de dx
    B.tm.runFrom (Cfg.ofWords (input := w) .lengthStart (emitterP2Words C.k D.k s u v)) t =
        Cfg.ofWords (.length dx) (emitterP2Words C.k D.k s u z) ∧
      splitSafe B.tm .anchor
        (Cfg.ofWords (input := w) .lengthStart (emitterP2Words C.k D.k s u v)) t := by
  dsimp only
  have h := emitterP2_call_phase D.tm (emitterP2BodyTM C D hk hl ce cx de dx).tm
    (emitterP2RightIndex C.k D.k)
    ⟨EmitterP2State.length, by intro a b h; exact EmitterP2State.length.inj h⟩ .lengthStart .anchor
    (by simp) (by intro q; simp) de dx (fun _ _ => rfl)
    (fun _ hq _ _ => if_neg hq)
    (fun i => bufferTape (emitterP2Words C.k D.k s u [] i)) (fun _ => 0)
    (Cfg.ofWords de (stateWord D.k v)) (Cfg.ofWords dx (stateWord D.k z)) rfl t ht hf hr
  dsimp only at h
  erw [emitterP2_right_frame, emitterP2_right_frame] at h
  exact h

/-- Compare both complete canonical words at head zero and retain the verdict
in finite control, without changing candidate, buffers, or module scratch.
**Proof sketch.** Relocate the comparator through its first observed return. The endpoint frame identities preserve the entire host layout and expose literal word equality in the controller. -/
private lemma emitterP2_body_compare (C D : FinTM Bool) (hk : 0 < C.k) (hl : 0 < D.k)
    (ce cx : C.State) (de dx : D.State) (w s u v : List Bool) :
    let B := emitterP2BodyTM C D hk hl ce cx de dx
    ∃ t ≤ 2 * (max u.length v.length + 1),
      B.tm.runFrom (Cfg.ofWords (input := w) (.compare (0, true))
        (emitterP2Words C.k D.k s u v)) t =
        Cfg.ofWords (.compare (2, decide (u = v))) (emitterP2Words C.k D.k s u v) ∧
      splitSafe B.tm .anchor (Cfg.ofWords (input := w) (.compare (0, true))
        (emitterP2Words C.k D.k s u v)) t := by
  dsimp only
  obtain ⟨t, _, ht, hf, hr⟩ := emitter_compare_first w u v 1
  have h := emitterP2_phase emitterCompareTM.tm (emitterP2BodyTM C D hk hl ce cx de dx).tm
    (emitterP2PairIndex C.k D.k hk hl)
    ⟨EmitterP2State.compare, by intro a b h; exact EmitterP2State.compare.inj h⟩ .anchor
    (by intro q; simp) (fun q : Fin 3 × Bool => q.1 ≠ 2)
    (fun _ hq _ _ => if_neg hq)
    (fun i => bufferTape (emitterP2Words C.k D.k s [] [] i)) (fun _ => 0)
    (emitterCompareCfg w u v 1 0 true 0) (emitterCompareCfg w u v 1 2 (decide (u = v)) 0) t
    (by intro j hj q hq he; rcases q with ⟨q, b⟩; dsimp at he; subst q; exact hf j hj b hq) hr
  erw [emitterP2_pair_frame _ _ hk hl, emitterP2_pair_frame _ _ hk hl] at h
  exact ⟨t, ht, h⟩
/-- Erase the complete installed width word, retain the verdict, and preserve
all other tapes. The module's scratch was already restored by its call.
**Proof sketch.** Relocate the contiguous-word eraser onto the first width-bank tape. A singleton-frame identity turns its exact blank return into a single word update, with the verdict retained in control. -/
private lemma emitterP2_body_erase_left (C D : FinTM Bool) (hk : 0 < C.k) (hl : 0 < D.k)
    (ce cx : C.State) (de dx : D.State) (w s u v : List Bool) (ok : Bool) :
    let B := emitterP2BodyTM C D hk hl ce cx de dx
    ∃ t ≤ 2 * (u.length + 1),
      B.tm.runFrom (Cfg.ofWords (input := w) (.eraseLeft ok 0)
        (emitterP2Words C.k D.k s u v)) t =
        Cfg.ofWords (.eraseLeft ok 2) (emitterP2Words C.k D.k s [] v) ∧
      splitSafe B.tm .anchor (Cfg.ofWords (input := w) (.eraseLeft ok 0)
        (emitterP2Words C.k D.k s u v)) t := by
  dsimp only
  let slot := emitterP2LeftIndex C.k D.k ⟨0, hk⟩
  let emb : Fin 3 ↪ EmitterP2State C.State D.State :=
    ⟨.eraseLeft ok, by intro a b h; exact (EmitterP2State.eraseLeft.inj h).2⟩
  let tapes := fun i => bufferTape (emitterP2Words C.k D.k s [] v i)
  have hframe (q : Fin 3) (a : List Bool) :
      (embedEmitCfg (emitterP2OneIndex slot) tapes (fun _ => 0) []
        (emitterP2EraseCfg w a q 0)).mapState emb =
          Cfg.ofWords (emb q) (emitterP2Words C.k D.k s a v) := by
    change (embedEmitCfg _ _ _ [] (Cfg.ofWords q (fun _ : Fin 1 => a))).mapState emb = _
    rw [emitterP2_one_frame, emitterP2_update_left]
  obtain ⟨t, _, ht, hf, hr⟩ := emitterP2_erase_first w u
  have h := emitterP2_phase emitterP2EraseTM.tm (emitterP2BodyTM C D hk hl ce cx de dx).tm
    (emitterP2OneIndex slot) emb .anchor
    (by intro q; simp [emb]) (fun q : Fin 3 => q ≠ 2)
    (by intro q hq inp work; simp [emb, slot, emitterP2BodyTM, hq])
    tapes (fun _ => 0) (emitterP2EraseCfg w u 0 0) (emitterP2EraseCfg w [] 2 0) t
    (by intro j hj q hq he; subst q; exact hf j hj hq) hr
  erw [hframe, hframe] at h
  exact ⟨t, ht, h⟩

/-- Erase the complete suffix-length word, retaining the verdict through the
last cleanup phase. All scratch and administrative words are now blank.
**Proof sketch.** Relocate the eraser onto the first length-bank tape. Its singleton-frame identity restores that whole word to blank and retains every other tape and the verdict. -/
private lemma emitterP2_body_erase_right (C D : FinTM Bool) (hk : 0 < C.k) (hl : 0 < D.k)
    (ce cx : C.State) (de dx : D.State) (w s u v : List Bool) (ok : Bool) :
    let B := emitterP2BodyTM C D hk hl ce cx de dx
    ∃ t ≤ 2 * (v.length + 1),
      B.tm.runFrom (Cfg.ofWords (input := w) (.eraseRight ok 0)
        (emitterP2Words C.k D.k s u v)) t =
        Cfg.ofWords (.eraseRight ok 2) (emitterP2Words C.k D.k s u []) ∧
      splitSafe B.tm .anchor (Cfg.ofWords (input := w) (.eraseRight ok 0)
        (emitterP2Words C.k D.k s u v)) t := by
  dsimp only
  let slot := emitterP2RightIndex C.k D.k ⟨0, hl⟩
  let emb : Fin 3 ↪ EmitterP2State C.State D.State :=
    ⟨.eraseRight ok, by intro a b h; exact (EmitterP2State.eraseRight.inj h).2⟩
  let tapes := fun i => bufferTape (emitterP2Words C.k D.k s u [] i)
  have hframe (q : Fin 3) (a : List Bool) :
      (embedEmitCfg (emitterP2OneIndex slot) tapes (fun _ => 0) []
        (emitterP2EraseCfg w a q 0)).mapState emb =
          Cfg.ofWords (emb q) (emitterP2Words C.k D.k s u a) := by
    change (embedEmitCfg _ _ _ [] (Cfg.ofWords q (fun _ : Fin 1 => a))).mapState emb = _
    rw [emitterP2_one_frame, emitterP2_update_right]
  obtain ⟨t, _, ht, hf, hr⟩ := emitterP2_erase_first w v
  have h := emitterP2_phase emitterP2EraseTM.tm (emitterP2BodyTM C D hk hl ce cx de dx).tm
    (emitterP2OneIndex slot) emb .anchor
    (by intro q; simp [emb]) (fun q : Fin 3 => q ≠ 2)
    (by intro q hq inp work; simp [emb, slot, emitterP2BodyTM, hq])
    tapes (fun _ => 0) (emitterP2EraseCfg w v 0 0) (emitterP2EraseCfg w [] 2 0) t
    (by intro j hj q hq he; subst q; exact hf j hj hq) hr
  erw [hframe, hframe] at h
  exact ⟨t, ht, h⟩

/-- The existing one-tape candidate advance enters at the canonical word seam. -/
private lemma emitterP2_advance_initial (w s : List Bool) :
    splitRestoreScan 0 w s 0 = Cfg.ofWords (0, false) (fun _ : Fin 1 => s) := by
  refine Cfg.ext ?_ ?_ ?_ ?_ rfl
  · simp [splitRestoreScan, Cfg.ofWords]
  · simp [splitRestoreScan, Cfg.ofWords, splitPos]
  · funext i; fin_cases i; rfl
  · funext i; rfl

/-- Every one-tape state word is the constant word function. -/
private lemma emitterP2_stateWord_one (s : List Bool) : stateWord 1 s = fun _ => s := by
  funext i; fin_cases i; rfl

/-- The existing candidate advance is relocated onto the preserved candidate
alone. It appends exactly within the input range, and otherwise stalls.
**Proof sketch.** Use the existing restoration theorem at zero scratch tapes, then relocate its sole candidate tape. Its full returned frame is the successor state word, with the out-of-range stall included. -/
private lemma emitterP2_body_advance (C D : FinTM Bool) (hk : 0 < C.k) (hl : 0 < D.k)
    (ce cx : C.State) (de dx : D.State) (w s : List Bool) :
    let B := emitterP2BodyTM C D hk hl ce cx de dx
    ∃ t ≤ 2 * s.length + w.length + 5,
      B.tm.runFrom (Cfg.ofWords (input := w) (.advance (0, false))
        (emitterP2Words C.k D.k s [] [])) t =
        Cfg.ofWords (.advance (4, false)) (emitterP2Words C.k D.k (splitStep w s) [] []) ∧
      splitSafe B.tm .anchor (Cfg.ofWords (input := w) (.advance (0, false))
        (emitterP2Words C.k D.k s [] [])) t := by
  dsimp only
  let emb : (Fin 5 × Bool) ↪ EmitterP2State C.State D.State :=
    ⟨.advance, by intro a b h; exact EmitterP2State.advance.inj h⟩
  let tapes := fun i => bufferTape (emitterP2Words C.k D.k [] [] [] i)
  obtain ⟨t, _, ht, hf, hr⟩ := splitRestore_first 0 w s
  have h := emitterP2_phase (splitRestoreTM 0).tm (emitterP2BodyTM C D hk hl ce cx de dx).tm
    (emitterP2OneIndex (0 : Fin (C.k + D.k + 1))) emb .anchor (by intro q; simp [emb])
    (fun q : Fin 5 × Bool => q ≠ (4, false))
    (by intro q hq inp work; simp [emb, emitterP2BodyTM, hq])
    tapes (fun _ => 0) (splitRestoreScan 0 w s 0)
    (Cfg.ofWords (4, false) (stateWord 1 (splitStep w s))) t
    (by intro j hj q hq he; subst q; exact hf j hj hq) hr
  rw [emitterP2_advance_initial, emitterP2_stateWord_one] at h
  dsimp only [tapes] at h
  erw [emitterP2_one_frame, emitterP2_one_frame,
    emitterP2_update_candidate, emitterP2_update_candidate] at h
  exact ⟨t, ht, h⟩

/-- The payload emitter's complete one-tape entry is the clean candidate seam. -/
private lemma emitterP2_emit_initial (w s : List Bool) :
    splitEmitCfg 0 w s (some 0) 0 0 [] = Cfg.ofWords 0 (fun _ : Fin 1 => s) := by
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · simp [splitEmitCfg, Cfg.ofWords, splitPos]
  · funext i; fin_cases i; rfl
  · funext i; fin_cases i; rfl

/-- Acceptance emits the split of the preserved native input, never the
candidate's bits. The exact emitter entry includes input head one and every
work head zero; unrelated banks remain blank throughout.
**Proof sketch.** Use the existing emitter at zero scratch tapes and relocate its sole candidate tape. Its full entry equality and native-input semantics give the stated payload and halt; disjoint emission control excludes the anchor. -/
private lemma emitterP2_body_emit (C D : FinTM Bool) (hk : 0 < C.k) (hl : 0 < D.k)
    (ce cx : C.State) (de dx : D.State) (w s : List Bool) (hs : s.length ≤ w.length) :
    let B := emitterP2BodyTM C D hk hl ce cx de dx
    let z := Cfg.ofWords (input := w) (.emit 0) (emitterP2Words C.k D.k s [] [])
    (B.tm.runFrom z (s.length + w.length + 3)).state = none ∧
      (B.tm.runFrom z (s.length + w.length + 3)).output =
        pairEncode (w.take s.length) (w.drop s.length) ∧
      splitSafe B.tm .anchor z (s.length + w.length + 3) := by
  dsimp only
  let emb : Fin 4 ↪ EmitterP2State C.State D.State :=
    ⟨.emit, by intro a b h; exact EmitterP2State.emit.inj h⟩
  let tapes := fun i => bufferTape (emitterP2Words C.k D.k [] [] [] i)
  have h := emitterP2_phase (splitEmitTM 0).tm (emitterP2BodyTM C D hk hl ce cx de dx).tm
    (emitterP2OneIndex (0 : Fin (C.k + D.k + 1))) emb .anchor (by intro q; simp [emb]) (fun _ => True)
    (fun _ _ _ _ => rfl) tapes (fun _ => 0)
    (splitEmitCfg 0 w s (some 0) 0 0 [])
    (splitEmitCfg 0 w s none w.length s.length (pairEncode (w.take s.length) (w.drop s.length)))
    (s.length + w.length + 3) (by intros; trivial) (splitEmit_run 0 w s hs)
  rw [emitterP2_emit_initial] at h
  dsimp only [tapes] at h
  erw [emitterP2_one_frame, emitterP2_update_candidate] at h
  exact ⟨congrArg Cfg.state h.1, congrArg Cfg.output h.1, h.2⟩
/-- Extend a safe phase by one silent dispatch to another non-anchor phase. -/
private lemma emitterP2_after {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c : Cfg k Bool S w)
    (t : ℕ) (q r : S) (words : Fin k → List Bool)
    (hr : tm.runFrom c t = Cfg.ofWords q words) (hs : splitSafe tm anchor c t)
    (htr : ∀ inp work, tm.tr q inp work = controlAction 0 (some r))
    (hq : q ≠ anchor) (hnext : r ≠ anchor) :
    tm.runFrom c (t + 1) = Cfg.ofWords r words ∧ splitSafe tm anchor c (t + 1) := by
  obtain ⟨he, hse⟩ := splitSafe_one tm anchor (Cfg.ofWords q words) (Cfg.ofWords r words)
    (emitterP2_control tm q r htr w words)
    (by simpa only [Cfg.ofWords, ne_eq, Option.some.injEq] using hq)
    (by simpa only [Cfg.ofWords, ne_eq, Option.some.injEq] using hnext)
  exact splitSafe_join tm anchor c _ _ t 1 hr hs he hse

/-- The two clean calls and comparison form one safe testing segment. Both
calls are charged before assuming any relation between their results.
**Proof sketch.** Concatenate the unconditional first-step calls and whole-word comparison with four explicit silent dispatches. Each complete frame is the next phase entry; the sum of their bounds includes both evaluator traces before testing equality. -/
private lemma emitterP2_body_test (C D : FinTM Bool) (hk : 0 < C.k) (hl : 0 < D.k)
    (ce cx : C.State) (de dx : D.State) (w s u v : List Bool)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hfC : ∀ j, 0 < j → j < a → (C.tm.runFrom
      (Cfg.ofWords (input := w) ce (stateWord C.k s)) j).state ≠ some cx)
    (hrC : C.tm.runFrom (Cfg.ofWords (input := w) ce (stateWord C.k s)) a =
      Cfg.ofWords cx (stateWord C.k u))
    (hfD : ∀ j, 0 < j → j < b → (D.tm.runFrom
      (Cfg.ofWords (input := w) de (stateWord D.k (w.drop s.length))) j).state ≠ some dx)
    (hrD : D.tm.runFrom (Cfg.ofWords (input := w) de (stateWord D.k (w.drop s.length))) b =
      Cfg.ofWords dx (stateWord D.k v)) :
    let B := emitterP2BodyTM C D hk hl ce cx de dx
    let z := Cfg.ofWords (input := w) (.prepare (8, false))
      (emitterP2Words C.k D.k s s (w.drop s.length))
    ∃ t ≤ a + b + 2 * (max u.length v.length + 1) + 4,
      B.tm.runFrom z t = Cfg.ofWords (.eraseLeft (decide (u = v)) 0)
        (emitterP2Words C.k D.k s u v) ∧ splitSafe B.tm .anchor z t := by
  dsimp only
  let tm := (emitterP2BodyTM C D hk hl ce cx de dx).tm
  let z := Cfg.ofWords (input := w) (EmitterP2State.prepare (S := C.State) (T := D.State) (8, false))
    (emitterP2Words C.k D.k s s (w.drop s.length))
  have hzsafe : splitSafe tm .anchor z 0 := by
    intro j hj
    have hz : j = 0 := by omega
    subst j
    simp [z, Cfg.ofWords]
  obtain ⟨h0, hs0⟩ := emitterP2_after tm .anchor z 0 (.prepare (8, false)) .widthStart _ rfl hzsafe
    (by intro inp work; simp [tm, emitterP2BodyTM]) (by simp) (by simp)
  obtain ⟨hE, hsE⟩ := emitterP2_body_width C D hk hl ce cx de dx w s u (w.drop s.length) a ha hfC hrC
  obtain ⟨h1, hs1⟩ := splitSafe_join tm .anchor z _ _ 1 a h0 hs0 hE hsE
  obtain ⟨h2, hs2⟩ := emitterP2_after tm .anchor z (1 + a) (.width cx) .lengthStart _ h1 hs1
    (by intro inp work; simp [tm, emitterP2BodyTM]) (by simp) (by simp)
  obtain ⟨hL, hsL⟩ := emitterP2_body_length C D hk hl ce cx de dx w s u (w.drop s.length) v b hb hfD hrD
  obtain ⟨h3, hs3⟩ := splitSafe_join tm .anchor z _ _ (1 + a + 1) b h2 hs2 hL hsL
  obtain ⟨h4, hs4⟩ := emitterP2_after tm .anchor z (1 + a + 1 + b) (.length dx) (.compare (0, true)) _ h3 hs3
    (by intro inp work; simp [tm, emitterP2BodyTM]) (by simp) (by simp)
  obtain ⟨c, hc, hQ, hsQ⟩ := emitterP2_body_compare C D hk hl ce cx de dx w s u v
  obtain ⟨h5, hs5⟩ := splitSafe_join tm .anchor z _ _ (1 + a + 1 + b + 1) c h4 hs4 hQ hsQ
  obtain ⟨h6, hs6⟩ := emitterP2_after tm .anchor z (1 + a + 1 + b + 1 + c)
    (.compare (2, decide (u = v))) (.eraseLeft (decide (u = v)) 0) _ h5 hs5
    (by intro inp work; simp [tm, emitterP2BodyTM]) (by simp) (by simp)
  exact ⟨1 + a + 1 + b + 1 + c + 1, by omega, h6, hs6⟩

/-- Cleanup and final dispatch close either branch at its literal target.
**Proof sketch.** Erase each installed word and retain the verdict in control.
Acceptance enters the complete native payload-emitter configuration. Rejection
runs the one-tape advance and makes one final silent anchor transition. Its
strict-interior exclusion includes every cleanup, rewind, and dispatch. -/
private lemma emitterP2_body_finish (C D : FinTM Bool) (hk : 0 < C.k) (hl : 0 < D.k)
    (ce cx : C.State) (de dx : D.State) (w s u v : List Bool) (ok : Bool)
    (hok : ok = true → s.length ≤ w.length) :
    let B := emitterP2BodyTM C D hk hl ce cx de dx
    let z := Cfg.ofWords (input := w) (.eraseLeft ok 0) (emitterP2Words C.k D.k s u v)
    ∃ t ≤ 2 * u.length + 2 * v.length + 2 * s.length + w.length + 12,
      (∀ j < t, (B.tm.runFrom z j).state ≠ some .anchor) ∧
      if ok then
        (B.tm.runFrom z t).state = none ∧
          (B.tm.runFrom z t).output = pairEncode (w.take s.length) (w.drop s.length)
      else B.tm.runFrom z t = Cfg.ofWords .anchor
        (emitterP2Words C.k D.k (splitStep w s) [] []) := by
  dsimp only
  let tm := (emitterP2BodyTM C D hk hl ce cx de dx).tm
  let z := Cfg.ofWords (input := w) (EmitterP2State.eraseLeft (S := C.State) (T := D.State) ok 0)
    (emitterP2Words C.k D.k s u v)
  obtain ⟨a, ha, h1, hs1⟩ := emitterP2_body_erase_left C D hk hl ce cx de dx w s u v ok
  obtain ⟨h2, hs2⟩ := emitterP2_after tm .anchor z a (.eraseLeft ok 2) (.eraseRight ok 0) _ h1 hs1
    (by intro inp work; simp [tm, emitterP2BodyTM]) (by simp) (by simp)
  obtain ⟨b, hb, hR, hsR⟩ := emitterP2_body_erase_right C D hk hl ce cx de dx w s [] v ok
  obtain ⟨h3, hs3⟩ := splitSafe_join tm .anchor z _ _ (a + 1) b h2 hs2 hR hsR
  cases ok with
  | false =>
    obtain ⟨h4, hs4⟩ := emitterP2_after tm .anchor z (a + 1 + b)
      (.eraseRight false 2) (.advance (0, false)) _ h3 hs3
      (by intro inp work; simp [tm, emitterP2BodyTM]) (by simp) (by simp)
    obtain ⟨c, hc, hA, hsA⟩ := emitterP2_body_advance C D hk hl ce cx de dx w s
    obtain ⟨h5, hs5⟩ := splitSafe_join tm .anchor z _ _ (a + 1 + b + 1) c h4 hs4 hA hsA
    have he := emitterP2_control tm (.advance (4, false)) .anchor
      (by intro inp work; simp [tm, emitterP2BodyTM]) w
      (emitterP2Words C.k D.k (splitStep w s) [] [])
    refine ⟨a + 1 + b + 1 + c + 1, by omega, ?_, ?_⟩
    · intro j hj; exact hs5 j (by omega)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      change tm.runFrom z (a + 1 + b + 1 + c + 1) = _
      rw [MultiTapeTM.runFrom_succ_eq_step', h5, he]
  | true =>
    obtain ⟨h4, hs4⟩ := emitterP2_after tm .anchor z (a + 1 + b)
      (.eraseRight true 2) (.emit 0) _ h3 hs3
      (by intro inp work; simp [tm, emitterP2BodyTM]) (by simp) (by simp)
    obtain ⟨he, ho, hse⟩ := emitterP2_body_emit C D hk hl ce cx de dx w s (hok rfl)
    have hsall : splitSafe tm .anchor z (a + 1 + b + 1 + (s.length + w.length + 3)) := by
      apply splitSafe_add tm .anchor z (a + 1 + b + 1) (s.length + w.length + 3) hs4
      rw [h4]; exact hse
    refine ⟨a + 1 + b + 1 + (s.length + w.length + 3), by omega,
      fun j hj => hsall j (by omega), ?_⟩
    simp only [↓reduceIte]
    change (tm.runFrom z _).state = none ∧ _
    rw [MultiTapeTM.runFrom_add, h4]
    exact ⟨he, ho⟩
/-- A safe prefix followed by a strictly safe terminal segment remains away
from the anchor before its final time, even when that final time returns. -/
private lemma emitterP2_strict_join {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c d : Cfg k Bool S w) (a b : ℕ)
    (hr : tm.runFrom c a = d) (hs : splitSafe tm anchor c a)
    (hf : ∀ j < b, (tm.runFrom d j).state ≠ some anchor) :
    ∀ j < a + b, (tm.runFrom c j).state ≠ some anchor := by
  intro j hj
  by_cases hja : j ≤ a
  · exact hs j hja
  · rw [show j = a + (j - a) by omega, MultiTapeTM.runFrom_add, hr]
    exact hf (j - a) (by omega)

/-- Full native round, parameterized by the two actual clean-call traces.
**Proof sketch.** Depart the anchor, prepare the exact two arguments, and
branch on the observed past-end flag. The past-end branch erases preparation
and returns silently. Otherwise run both calls before comparing their entire
binary answers. The verdict survives cleanup; the finish theorem emits the
native split or advances to the exact canonical seam. Every interior phase
excludes the anchor, and the one-step departure makes every round positive. -/
private lemma emitterP2_body_round (f : ℕ → ℕ) (C D : FinTM Bool)
    (hk : 0 < C.k) (hl : 0 < D.k) (ce cx : C.State) (de dx : D.State)
    (w s : List Bool) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hfC : ∀ j, 0 < j → j < a → (C.tm.runFrom
      (Cfg.ofWords (input := w) ce (stateWord C.k s)) j).state ≠ some cx)
    (hrC : C.tm.runFrom (Cfg.ofWords (input := w) ce (stateWord C.k s)) a =
      Cfg.ofWords cx (stateWord C.k (Nat.bits (f s.length))))
    (hfD : ∀ j, 0 < j → j < b → (D.tm.runFrom
      (Cfg.ofWords (input := w) de (stateWord D.k (w.drop s.length))) j).state ≠ some dx)
    (hrD : D.tm.runFrom (Cfg.ofWords (input := w) de (stateWord D.k (w.drop s.length))) b =
      Cfg.ofWords dx (stateWord D.k (Nat.bits (w.drop s.length).length))) :
    let B := emitterP2BodyTM C D hk hl ce cx de dx
    let z := Cfg.ofWords (input := w) .anchor (stateWord B.k s)
    ∃ t, 0 < t ∧
      t ≤ a + b + 10 * (s.length + w.length + (Nat.bits (f s.length)).length +
        (Nat.bits (w.drop s.length).length).length + 10) ∧
      (∀ j, 0 < j → j < t → (B.tm.runFrom z j).state ≠ some .anchor) ∧
      if emitterSplitAccept f w s then
        (B.tm.runFrom z t).state = none ∧
          (B.tm.runFrom z t).output = pairEncode (w.take s.length) (w.drop s.length)
      else B.tm.runFrom z t = Cfg.ofWords .anchor (stateWord B.k (splitStep w s)) := by
  dsimp only
  let tm := (emitterP2BodyTM C D hk hl ce cx de dx).tm
  let z := Cfg.ofWords (input := w) (EmitterP2State.anchor (S := C.State) (T := D.State))
    (stateWord (C.k + D.k + 1) s)
  let p := Cfg.ofWords (input := w) (EmitterP2State.prepare (S := C.State) (T := D.State) (0, false))
    (emitterP2Words C.k D.k s [] [])
  have hdepart : tm.runFrom z 1 = p := by
    change tm.step z = p
    simpa only [z, p, emitterP2_words_clean] using emitterP2_control tm .anchor (.prepare (0, false))
      (fun _ _ => rfl) w (emitterP2Words C.k D.k s [] [])
  obtain ⟨c, hc, hp, hps⟩ := emitterP2_body_prepare C D hk hl ce cx de dx w s
  by_cases hover : w.length < s.length
  · have hp' : tm.runFrom p c = Cfg.ofWords (.prepare (8, true))
        (emitterP2Words C.k D.k s s (w.drop s.length)) := by simpa [hover] using hp
    obtain ⟨h2, hs2⟩ := emitterP2_after tm .anchor p c (.prepare (8, true)) (.eraseLeft false 0)
      _ hp' hps (by intro inp work; simp [tm, emitterP2BodyTM]) (by simp) (by simp)
    obtain ⟨d, hd, hds, hfinish⟩ := emitterP2_body_finish C D hk hl ce cx de dx w s s
      (w.drop s.length) false (by simp)
    have hstrict := emitterP2_strict_join tm .anchor p _ (c + 1) d h2 hs2 hds
    have hrun : tm.runFrom z (1 + (c + 1 + d)) = tm.runFrom
        (Cfg.ofWords (.eraseLeft false 0) (emitterP2Words C.k D.k s s (w.drop s.length))) d := by
      rw [MultiTapeTM.runFrom_add, hdepart, MultiTapeTM.runFrom_add, h2]
    refine ⟨1 + (c + 1 + d), by omega, ?_, ?_, ?_⟩
    · have hv : (w.drop s.length).length ≤ w.length := by simp only [List.length_drop]; omega
      omega
    · intro j hj hjt
      change (tm.runFrom z j).state ≠ _
      rw [show j = 1 + (j - 1) by omega, MultiTapeTM.runFrom_add, hdepart]
      exact hstrict (j - 1) (by omega)
    · have hn : s.length + f s.length ≠ w.length := by omega
      simp only [emitterSplitAccept, hn, decide_false, Bool.false_eq_true, ↓reduceIte]
      change tm.runFrom z (1 + (c + 1 + d)) = _
      rw [hrun]
      simpa only [Bool.false_eq_true, ↓reduceIte, emitterP2_words_clean] using hfinish
  · have hs : s.length ≤ w.length := by omega
    have hp' : tm.runFrom p c = Cfg.ofWords (.prepare (8, false))
        (emitterP2Words C.k D.k s s (w.drop s.length)) := by simpa [hover] using hp
    let u := Nat.bits (f s.length)
    let v := Nat.bits (w.drop s.length).length
    obtain ⟨d, hd, htest, htests⟩ := emitterP2_body_test C D hk hl ce cx de dx w s u v
      a b ha hb hfC hrC hfD hrD
    obtain ⟨h2, hs2⟩ := splitSafe_join tm .anchor p _ _ c d hp' hps htest htests
    obtain ⟨e, he, hes, hfinish⟩ := emitterP2_body_finish C D hk hl ce cx de dx w s u v
      (decide (u = v)) (fun _ => hs)
    have hstrict := emitterP2_strict_join tm .anchor p _ (c + d) e h2 hs2 hes
    have hrun : tm.runFrom z (1 + (c + d + e)) = tm.runFrom
        (Cfg.ofWords (.eraseLeft (decide (u = v)) 0) (emitterP2Words C.k D.k s u v)) e := by
      rw [MultiTapeTM.runFrom_add, hdepart, MultiTapeTM.runFrom_add, h2]
    have hok : decide (u = v) = emitterSplitAccept f w s := by
      apply Bool.eq_iff_iff.mpr
      simpa only [u, v, emitterSplitAccept, decide_eq_true_eq] using emitter_binary_check f w s hs
    refine ⟨1 + (c + d + e), by omega, ?_, ?_, ?_⟩
    · have hm : max u.length v.length ≤ u.length + v.length := max_le (by omega) (by omega)
      change 1 + (c + d + e) ≤ a + b + 10 * (s.length + w.length + u.length + v.length + 10)
      omega
    · intro j hj hjt
      change (tm.runFrom z j).state ≠ _
      rw [show j = 1 + (j - 1) by omega, MultiTapeTM.runFrom_add, hdepart]
      exact hstrict (j - 1) (by omega)
    · change if emitterSplitAccept f w s then
        (tm.runFrom z (1 + (c + d + e))).state = none ∧
          (tm.runFrom z (1 + (c + d + e))).output = _
        else tm.runFrom z (1 + (c + d + e)) = _
      rw [hrun]
      simpa only [hok, emitterP2_words_clean] using hfinish
/-- Extract the two clean-call modules once, fix their layout, and close the
frozen split contract through the existing result-bearing loop.
**Proof sketch.** Apply the width evaluator only to the actual candidate and
the length evaluator only to the actual native suffix. Bound each returned
word by its own evaluator deadline, then enlarge those analysis bounds to
the common input-length envelope. The concrete round theorem supplies every
canonical endpoint and strict-interior exclusion. Neither deadline occurs in
the controller; dispatch follows the proved first-positive return instead. -/
private lemma emitterP2_closed (f : ℕ → ℕ) (E : FinTM Bool) (TE : ℕ → ℕ)
    (hTE : Monotone TE) (hE : E.ComputesFunInTime (fun s => Nat.bits (f s.length)) TE) :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime
      (fun w => match solveSplitWith f w.length with
        | some i => pairEncode (w.take i) (w.drop i)
        | none => [])
      (fun n => c * (n + 1) * (TE (n + 1) + n + 2)) := by
  obtain ⟨L, d, hL⟩ := computesFunInTime_lengthBits
  obtain ⟨C, ce, cx, cC, hk, hC⟩ :=
    exists_installCallTM E (fun s => Nat.bits (f s.length)) TE hE
  obtain ⟨D, de, dx, cD, hl, hD⟩ :=
    exists_installCallTM L (fun s => Nat.bits s.length) (fun n => d * (n + 1)) hL
  let B := emitterP2BodyTM C D hk hl ce cx de dx
  let A := 2 * cC + cD * (2 * d + 1) + 10 * (d + 8)
  apply emitterSplit_of_body f TE B .anchor A
  · intro w
    refine ⟨0, Nat.zero_le _, ?_, ?_⟩
    · intro j hj; omega
    · exact emitterP2_body_start C D hk hl ce cx de dx w
  · intro w s hs
    let H := TE (w.length + 1) + w.length + 2
    let u := Nat.bits (f s.length)
    let v := Nat.bits (w.drop s.length).length
    obtain ⟨_, hu, hmono⟩ := emitter_width_budget f E TE hTE hE w s hs
    have hdrop : (w.drop s.length).length ≤ w.length := by simp only [List.length_drop]; omega
    have hv : v.length ≤ d * ((w.drop s.length).length + 1) := by
      have hout := ((computesInTime_iff _ _ _ _).mp (hL (w.drop s.length))).2
      simpa only [hout, v] using L.tm.output_length_le (w.drop s.length)
        (d * ((w.drop s.length).length + 1))
    obtain ⟨a, ha, hap, haf, har⟩ := hC w s
    obtain ⟨b, hb, hbp, hbf, hbr⟩ := hD w (w.drop s.length)
    obtain ⟨t, htpos, ht, hfirst, hr⟩ := emitterP2_body_round f C D hk hl ce cx de dx
      w s a b hap hbp haf har hbf hbr
    refine ⟨t, htpos, ?_, hfirst, hr⟩
    have hHs : s.length ≤ H := by dsimp [H]; omega
    have hHn : w.length ≤ H := by dsimp [H]; omega
    have hHu : u.length ≤ H := by dsimp [u, H]; omega
    have hHfive : 10 ≤ 5 * H := by dsimp [H]; omega
    have hLd : d * ((w.drop s.length).length + 1) ≤ d * H :=
      Nat.mul_le_mul_left d (by dsimp [H]; omega)
    have hHv : v.length ≤ d * H := hv.trans hLd
    have hCa : TE s.length + s.length + u.length + 1 ≤ 2 * H := by
      dsimp [u, H]; omega
    have hCa' : a ≤ (2 * cC) * H := by
      calc
        a ≤ cC * (TE s.length + s.length + u.length + 1) := ha
        _ ≤ cC * (2 * H) := Nat.mul_le_mul_left _ hCa
        _ = (2 * cC) * H := by ring
    have hDb : d * ((w.drop s.length).length + 1) + (w.drop s.length).length + v.length + 1 ≤
        (2 * d + 1) * H := by
      calc
        _ ≤ 2 * (d * H) + H := by dsimp [H] at *; omega
        _ = (2 * d + 1) * H := by ring
    have hDb' : b ≤ (cD * (2 * d + 1)) * H := by
      calc
        b ≤ cD * (d * ((w.drop s.length).length + 1) + (w.drop s.length).length + v.length + 1) := hb
        _ ≤ cD * ((2 * d + 1) * H) := Nat.mul_le_mul_left _ hDb
        _ = (cD * (2 * d + 1)) * H := by ring
    have hsum : s.length + w.length + u.length + v.length + 10 ≤ (d + 8) * H := by
      rw [Nat.add_mul]
      omega
    calc
      t ≤ a + b + 10 * (s.length + w.length + u.length + v.length + 10) := ht
      _ ≤ (2 * cC) * H + (cD * (2 * d + 1)) * H + 10 * ((d + 8) * H) :=
        Nat.add_le_add (Nat.add_le_add hCa' hDb') (Nat.mul_le_mul_left _ hsum)
      _ = A * (TE (w.length + 1) + w.length + 2) := by dsimp [A, H]; ring

/-- **The width-parametric split search's time**. If `E` computes `s ↦ Nat.bits (f |s|)` within a
monotone `TE`, the split search computes `w ↦ pairEncode (w.take i) (w.drop i)` for the first
solution `i` of `i + f i = |w|` (`Turing.solveSplitWith`), and `[]` if there is none, within
`20·(591 + 26·k_E)·(n + 1)·(TE (n + 1) + n + 2)` steps.

**Proof sketch.** Today's `emitterP2_closed` and `emitterSplit_of_body` with every existential
named: the clean calls cost `(24 + 13·k_E)` and `(24 + 13·1)` times their arguments
(`callTM_run`), the round coefficient is `A = 2(24 + 13·k_E) + 37·11 + 10·13 = 585 + 26·k_E`
(`emitterP2_body_round`, `emitter_width_budget`), the counter's `5` enlarges it, and
`emitterSplit_loop_bound` turns the find loop's `10·(T n + 1)·(n + 2)` into
`2·10·(A + 6)·(n + 1)·(TE (n + 1) + n + 2)`. -/
theorem splitSolveWithTM_computes (f : ℕ → ℕ) (E : FinTM Bool) (TE : ℕ → ℕ)
    (hTE : Monotone TE) (hE : E.ComputesFunInTime (fun s => Nat.bits (f s.length)) TE) :
    (splitSolveWithTM E).ComputesFunInTime
      (fun w => match solveSplitWith f w.length with
        | some i => pairEncode (w.take i) (w.drop i)
        | none => [])
      (fun n => 20 * (591 + 26 * E.k) * (n + 1) * (TE (n + 1) + n + 2)) := by
  let C := callTM E false
  let D := callTM lengthBitsTM false
  let B := emitterP2BodyTM C D (callTM_k_pos E false) (callTM_k_pos lengthBitsTM false)
    (callEntry E false) (callExit E false) (callEntry lengthBitsTM false)
    (callExit lengthBitsTM false)
  let A := 2 * (24 + 13 * E.k) + (24 + 13 * lengthBitsTM.k) * (2 * 5 + 1) + 10 * (5 + 8)
  -- the install-call contracts of the two named calls, from `callTM_run`
  have hCall (M : FinTM Bool) (g : List Bool → List Bool) (Tg : ℕ → ℕ)
      (hg : M.ComputesFunInTime g Tg) (x arg : List Bool) :
      ∃ t ≤ (24 + 13 * M.k) * (Tg arg.length + arg.length + (g arg).length + 1), 0 < t ∧
        (∀ t', 0 < t' → t' < t → ((callTM M false).tm.runFrom
          (Cfg.ofWords (input := x) (callEntry M false) (stateWord (callTM M false).k arg))
            t').state ≠ some (callExit M false)) ∧
        (callTM M false).tm.runFrom
          (Cfg.ofWords (input := x) (callEntry M false) (stateWord (callTM M false).k arg)) t =
            Cfg.ofWords (callExit M false) (stateWord (callTM M false).k (g arg)) := by
    obtain ⟨t, ht, hpos, hfirst, hr⟩ := callTM_run M false x arg (g arg) (Tg arg.length) (hg arg)
    exact ⟨t, ht, hpos, fun j _ hj => hfirst j hj, by simpa using hr⟩
  have hstart : ∀ w : List Bool, ∃ t ≤ (A + 5) * (TE (w.length + 1) + w.length + 2),
      (∀ t' < t, (B.tm.runFrom (B.tm.initCfg w) t').state ≠ some .anchor) ∧
      B.tm.runFrom (B.tm.initCfg w) t = Cfg.ofWords .anchor (stateWord B.k []) := fun w =>
    ⟨0, Nat.zero_le _, fun j hj => absurd hj (Nat.not_lt_zero _),
      emitterP2_body_start C D _ _ _ _ _ _ w⟩
  have hround : ∀ (w s : List Bool), s.length ≤ w.length + 1 →
      ∃ t, 0 < t ∧ t ≤ (A + 5) * (TE (w.length + 1) + w.length + 2) ∧
        (∀ t', 0 < t' → t' < t →
          (B.tm.runFrom (Cfg.ofWords (input := w) .anchor (stateWord B.k s)) t').state
            ≠ some .anchor) ∧
        if emitterSplitAccept f w s then
          (B.tm.runFrom (Cfg.ofWords (input := w) .anchor (stateWord B.k s)) t).state = none ∧
          (B.tm.runFrom (Cfg.ofWords (input := w) .anchor (stateWord B.k s)) t).output =
            pairEncode (w.take s.length) (w.drop s.length)
        else
          B.tm.runFrom (Cfg.ofWords (input := w) .anchor (stateWord B.k s)) t =
            Cfg.ofWords .anchor (stateWord B.k (splitStep w s)) := by
    intro w s hs
    have hL := lengthBitsTM_computes
    let H := TE (w.length + 1) + w.length + 2
    let u := Nat.bits (f s.length)
    let v := Nat.bits (w.drop s.length).length
    obtain ⟨_, hu, hmono⟩ := emitter_width_budget f E TE hTE hE w s hs
    have hdrop : (w.drop s.length).length ≤ w.length := by
      simp only [List.length_drop]; omega
    have hv : v.length ≤ 5 * ((w.drop s.length).length + 1) := by
      have hout := ((computesInTime_iff _ _ _ _).mp (hL (w.drop s.length))).2
      simpa only [hout, v] using lengthBitsTM.tm.output_length_le (w.drop s.length)
        (5 * ((w.drop s.length).length + 1))
    obtain ⟨a, ha, hap, haf, har⟩ := hCall E (fun s => Nat.bits (f s.length)) TE hE w s
    obtain ⟨b, hb, hbp, hbf, hbr⟩ :=
      hCall lengthBitsTM (fun s => Nat.bits s.length) (fun n => 5 * (n + 1)) hL w
        (w.drop s.length)
    obtain ⟨t, htpos, ht, hfirst, hr⟩ := emitterP2_body_round f C D _ _ _ _ _ _
      w s a b hap hbp haf har hbf hbr
    refine ⟨t, htpos, ?_, hfirst, hr⟩
    have hHs : s.length ≤ H := by dsimp [H]; omega
    have hHn : w.length ≤ H := by dsimp [H]; omega
    have hHu : u.length ≤ H := by dsimp [u, H]; omega
    have hLd : 5 * ((w.drop s.length).length + 1) ≤ 5 * H :=
      Nat.mul_le_mul_left 5 (by dsimp [H]; omega)
    have hHv : v.length ≤ 5 * H := hv.trans hLd
    have hCa : TE s.length + s.length + u.length + 1 ≤ 2 * H := by
      dsimp [u, H]; omega
    have hCa' : a ≤ (2 * (24 + 13 * E.k)) * H := by
      calc
        a ≤ (24 + 13 * E.k) * (TE s.length + s.length + u.length + 1) := ha
        _ ≤ (24 + 13 * E.k) * (2 * H) := Nat.mul_le_mul_left _ hCa
        _ = (2 * (24 + 13 * E.k)) * H := by ring
    have hDb : 5 * ((w.drop s.length).length + 1) + (w.drop s.length).length + v.length + 1 ≤
        (2 * 5 + 1) * H := by
      dsimp [H] at *; omega
    have hDb' : b ≤ ((24 + 13 * lengthBitsTM.k) * (2 * 5 + 1)) * H := by
      calc
        b ≤ (24 + 13 * lengthBitsTM.k) *
            (5 * ((w.drop s.length).length + 1) + (w.drop s.length).length + v.length + 1) :=
          hb
        _ ≤ (24 + 13 * lengthBitsTM.k) * ((2 * 5 + 1) * H) := Nat.mul_le_mul_left _ hDb
        _ = ((24 + 13 * lengthBitsTM.k) * (2 * 5 + 1)) * H := by ring
    have hsum : s.length + w.length + u.length + v.length + 10 ≤ (5 + 8) * H := by
      rw [Nat.add_mul]
      omega
    calc
      t ≤ a + b + 10 * (s.length + w.length + u.length + v.length + 10) := ht
      _ ≤ (2 * (24 + 13 * E.k)) * H + ((24 + 13 * lengthBitsTM.k) * (2 * 5 + 1)) * H +
          10 * ((5 + 8) * H) :=
        Nat.add_le_add (Nat.add_le_add hCa' hDb') (Nat.mul_le_mul_left _ hsum)
      _ = A * H := by dsimp [A]; ring
      _ ≤ (A + 5) * H := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  have hF : lengthBitsTM.ComputesFunInTime (fun w => Nat.bits (id w.length))
      (fun n => (A + 5) * (TE (n + 1) + n + 2)) := by
    intro w
    refine (lengthBitsTM_computes w).mono ?_
    exact (Nat.mul_le_mul_left 5 (by omega : w.length + 1 ≤
      TE (w.length + 1) + w.length + 2)).trans (Nat.mul_le_mul_right _ (by omega))
  have hM := loopHostTM_finds B lengthBitsTM .anchor
    (fun w s => s.length ≤ w.length + 1) splitStep (emitterSplitAccept f)
    (fun w s => pairEncode (w.take s.length) (w.drop s.length)) (fun _ => [])
    id (fun n => (A + 5) * (TE (n + 1) + n + 2)) hF (by intro w; simp) splitStep_inv
    hstart hround
  intro w
  have hm := hM w
  dsimp only [id_eq] at hm
  have hb : 10 * ((A + 5) * (TE (w.length + 1) + w.length + 2) + 1) * (w.length + 2) ≤
      20 * (591 + 26 * E.k) * (w.length + 1) * (TE (w.length + 1) + w.length + 2) :=
    (emitterSplit_loop_bound 10 (A + 5) w.length (TE (w.length + 1))).trans
      (le_of_eq (by simp only [A, show lengthBitsTM.k = 1 from rfl]; ring))
  convert hm.mono hb using 1
  exact (emitterSplit_result f w).symm

/-- **E4′, width-parametric split search** (design
§11; customers: 3A-cont's exponential padding equation — whose bespoke
body is this contract's harvest template — and every later padding
argument, including the ch3 hierarchy theorems). The generalization of
`Turing.FinTM.computesFunInTime_splitSolve` from the hardwired polynomial
family to a hypothesis-supplied width evaluator: given a machine `E`
computing the binary representation of `f` of the input length within a
monotone budget `TE`, a machine solving `i + f i = n` by first-success
search, emitting the threaded split of the original input, and `[]` on
exhaustion, inside the loopFind envelope over `TE`. At
`f = fun i => C * (i + 1) ^ e` the computed function definitionally
recovers the catalog split's.

**Construction sketch.** The `exists_loopFindTM` engine with candidate
word as loop state: per round, run `E` on the prepared candidate prefix
with captured output (charging `TE` before any validity check), compare
whole canonical binary words against the suffix length, restore scratch,
advance by one; the one-past-end candidate takes a positive silent
stall. 3A-cont's displayed body contracts are exactly this round
discipline. -/
theorem computesFunInTime_splitSolveWith (f : ℕ → ℕ) (E : FinTM Bool)
    (TE : ℕ → ℕ) (hTE : Monotone TE)
    (hE : E.ComputesFunInTime (fun s => Nat.bits (f s.length)) TE) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun w => match solveSplitWith f w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => [])
        fun n => c * (n + 1) * (TE (n + 1) + n + 2) := by
  exact emitterP2_closed f E TE hTE hE

/-- **The unary token splitter**. A machine with no work tapes that, in one left-to-right scan,
emits the leading unary token of its input (the `true`s up to and including the first `false`)
doubled, then the pair separator, then the rest of the input, so that it outputs `pairEncode` of
`Turing.unaryTokenSplit x`. -/
def unaryTokenTM : FinTM Bool where
  k := 0
  State := Fin 6
  tm :=
    { q₀ := 0
      tr := fun q inp _ => match q.val with
        | 0 => match inp with
          | some b => ⟨0, fun j => j.elim0, some b, some (if b then 1 else 2)⟩
          | none => ⟨0, fun j => j.elim0, some false, some 4⟩
        | 1 => ⟨.pos, fun j => j.elim0, some true, some 0⟩
        | 2 => ⟨.pos, fun j => j.elim0, some false, some 3⟩
        | 3 => ⟨0, fun j => j.elim0, some false, some 4⟩
        | 4 => ⟨0, fun j => j.elim0, some true, some 5⟩
        | _ => match inp with
          | some b => ⟨.pos, fun j => j.elim0, some b, some 5⟩
          | none => ⟨0, fun j => j.elim0, none, none⟩ }

/-- Two token transitions double the next bit and advance the input once;
only a false bit ends token scanning. -/
private lemma emitterToken_double (x pre rest out : List Bool) (b : Bool)
    (hx : x = pre ++ b :: rest) :
    unaryTokenTM.tm.runFrom
      (scanCfg x (some (0 : Fin 6)) pre.length (by simp [hx]) out) 2 =
      scanCfg x (some (if b then (0 : Fin 6) else 3)) (pre ++ [b]).length
        (by simp [hx]) (out ++ [b, b]) := by
  have hlen : pre.length < x.length := by simp [hx]
  have hread : x[pre.length]? = some b := by simp [hx]
  have hfirst : unaryTokenTM.tm.step
      (scanCfg x (some (0 : Fin 6)) pre.length (by omega) out) =
      scanCfg x (some (if b then (1 : Fin 6) else 2)) pre.length (by omega)
        (out ++ [b]) := by
    unfold MultiTapeTM.step
    change (unaryTokenTM.tm.tr (0 : Fin 6) _ _).apply _ = _
    rw [scanCfg_read, hread]
    apply Cfg.ext_zero_tapes <;> simp [unaryTokenTM, Action.apply, scanCfg]
  rw [show 2 = 1 + 1 by omega, MultiTapeTM.runFrom_succ_eq_step',
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero, hfirst]
  cases b <;>
    apply Cfg.ext_zero_tapes
  all_goals first
    | rfl
    | simpa [MultiTapeTM.step, unaryTokenTM, Action.apply, scanCfg] using
        moveInputPos_pos_of_ne_right
          (⟨pre.length + 1, by omega⟩ : Fin (x.length + 2)) (by simp; omega)
    | simp [MultiTapeTM.step, unaryTokenTM, Action.apply, scanCfg, List.append_assoc]

/-- The two separator transitions preserve the input position and append the
unique pair delimiter before entering the suffix copier. -/
private lemma emitterToken_separator (x out : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    unaryTokenTM.tm.runFrom (scanCfg x (some (3 : Fin 6)) i hi out) 2 =
      scanCfg x (some (5 : Fin 6)) i hi (out ++ [false, true]) := by
  rw [show 2 = 1 + 1 by omega, MultiTapeTM.runFrom_succ_eq_step',
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
  apply Cfg.ext_zero_tapes <;>
    simp [MultiTapeTM.step, unaryTokenTM, Action.apply, scanCfg, List.append_assoc]

/-- The streaming token encoder emits the exact recursive split, after any
already-consumed prefix. Its time is twice the token length plus the remainder
length plus three, including the final blank-reading halt.
**Proof sketch.** Induct on the unconsumed input. At the right blank emit just
the separator. A false bit is doubled and terminates the token, so emit the
separator and copy the suffix. A true bit is doubled and the induction
hypothesis processes the remaining token. No standalone marker is consumed. -/
private lemma emitterToken_run (x rest : List Bool) :
    ∀ pre out (hx : x = pre ++ rest),
      unaryTokenTM.tm.runFrom
        (scanCfg x (some (0 : Fin 6)) pre.length (by simp [hx]) out)
        (2 * (unaryTokenSplit rest).1.length + (unaryTokenSplit rest).2.length + 3) =
        scanCfg x none x.length (by omega)
          (out ++ pairEncode (unaryTokenSplit rest).1 (unaryTokenSplit rest).2) := by
  induction rest with
  | nil =>
    intro pre out hx
    have hlen : pre.length = x.length := by simp [hx]
    have hread : x[pre.length]? = none := by simp [hlen]
    simp only [unaryTokenSplit, List.length_nil, Nat.mul_zero, Nat.zero_add]
    have hfirst : unaryTokenTM.tm.step
        (scanCfg x (some (0 : Fin 6)) pre.length (by omega) out) =
        scanCfg x (some (4 : Fin 6)) pre.length (by omega) (out ++ [false]) := by
      unfold MultiTapeTM.step
      change (unaryTokenTM.tm.tr (0 : Fin 6) _ _).apply _ = _
      rw [scanCfg_read, hread]
      apply Cfg.ext_zero_tapes <;> simp [unaryTokenTM, Action.apply, scanCfg]
    have hsecond : unaryTokenTM.tm.step
        (scanCfg x (some (4 : Fin 6)) pre.length (by omega) (out ++ [false])) =
        scanCfg x (some (5 : Fin 6)) pre.length (by omega) (out ++ [false, true]) := by
      apply Cfg.ext_zero_tapes <;>
        simp [MultiTapeTM.step, unaryTokenTM, Action.apply, scanCfg, List.append_assoc]
    rw [show 3 = (0 + 1) + 1 + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero, hfirst, hsecond]
    unfold MultiTapeTM.step
    change (unaryTokenTM.tm.tr (5 : Fin 6) _ _).apply _ = _
    rw [scanCfg_read, hread]
    apply Cfg.ext_zero_tapes <;>
      simp [unaryTokenTM, Action.apply, scanCfg, pairEncode, List.append_assoc, hlen]
  | cons b rest ih =>
    intro pre out hx
    cases b with
    | false =>
      simp only [unaryTokenSplit, List.length_cons, List.length_nil]
      rw [show 2 * (0 + 1) + rest.length + 3 = 2 + (2 + (rest.length + 1)) by omega,
        MultiTapeTM.runFrom_add, emitterToken_double x pre rest out false hx]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [MultiTapeTM.runFrom_add, emitterToken_separator]
      have he := scanCopy_suffix unaryTokenTM.tm (5 : Fin 6) (fun _ _ => rfl)
        x rest (pre ++ [false]) ((out ++ [false, false]) ++ [false, true])
        (by simpa only [List.append_assoc, List.singleton_append] using hx)
      simpa [pairEncode, List.append_assoc] using he
    | true =>
      simp only [unaryTokenSplit, List.length_cons]
      rw [show 2 * ((unaryTokenSplit rest).1.length + 1) +
          (unaryTokenSplit rest).2.length + 3 =
          2 + (2 * (unaryTokenSplit rest).1.length + (unaryTokenSplit rest).2.length + 3)
          by omega,
        MultiTapeTM.runFrom_add, emitterToken_double x pre rest out true hx]
      simp only [↓reduceIte]
      have he := ih (pre ++ [true]) (out ++ [true, true])
        (by simpa only [List.append_assoc, List.singleton_append] using hx)
      simpa [pairEncode, List.append_assoc] using he

/-- Token and remainder partition every input, including empty and
unterminated tokens, so their lengths sum to the original length. -/
private lemma emitterToken_length (x : List Bool) :
    (unaryTokenSplit x).1.length + (unaryTokenSplit x).2.length = x.length := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> simp_all [unaryTokenSplit] <;> omega

/-- **The token splitter's time**. The splitter computes
`x ↦ pairEncode (unaryTokenSplit x).1 (unaryTokenSplit x).2` within `3·(n + 1)` steps.

**Proof sketch.** The body of today's `computesFunInTime_unaryToken`: the private scan lemma
`emitterToken_run` reaches the halt in `2·|token| + |rest| + 3` steps, and `|token| + |rest| = |x|`
(`emitterToken_length`). -/
theorem unaryTokenTM_computes :
    unaryTokenTM.ComputesFunInTime
      (fun x => pairEncode (unaryTokenSplit x).1 (unaryTokenSplit x).2)
      (fun n => 3 * (n + 1)) := by
  sorry

/-- **P16, the unary token step** (design §11;
customers: 3B-cont's streaming scanner, the Cook-Levin emitter's index
reads (4A), 4B's dual scanner — the fourth re-derivation of this atom
otherwise, after 2D's parsers, 3B's `satScanTM`, and 3D's six-state
scan). Split off the leading unary token (`Turing.unaryTokenSplit`) as a
self-delimiting pair, in linear time.

**Construction sketch.** One left-to-right scan emitting the token bits
as read, the delimiter, the pair framing, and the remainder — the proved
scanner stages of the 3B and 3D deliveries are the harvest sources. -/
theorem computesFunInTime_unaryToken :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun x => pairEncode (unaryTokenSplit x).1 (unaryTokenSplit x).2)
        fun n => c * (n + 1) := by
  refine ⟨unaryTokenTM, 3, fun x => ?_⟩
  have hr := emitterToken_run x x [] [] rfl
  have hc : unaryTokenTM.ComputesInTime x
      (pairEncode (unaryTokenSplit x).1 (unaryTokenSplit x).2)
      (2 * (unaryTokenSplit x).1.length + (unaryTokenSplit x).2.length + 3) := by
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    have hinit : unaryTokenTM.tm.initCfg x =
        scanCfg x (some (0 : Fin 6)) 0 (by omega) [] := by
      apply Cfg.ext_zero_tapes <;> simp [unaryTokenTM, scanCfg]
    rw [hinit]
    constructor
    · simpa only [List.length_nil, scanCfg] using congrArg Cfg.state hr
    · simpa only [List.length_nil, List.nil_append, scanCfg] using congrArg Cfg.output hr
  apply hc.mono
  change 2 * (unaryTokenSplit x).1.length + (unaryTokenSplit x).2.length + 3 ≤
    3 * (x.length + 1)
  have hl := emitterToken_length x
  omega

/-- **The bit appender**. A machine with no work tapes that copies its input and emits the fixed bit
`b` on the halting transition, so that it computes `x ↦ x ++ [b]`. -/
def appendBitTM (b : Bool) : FinTM Bool where
  k := 0
  State := Unit
  tm :=
    { q₀ := ()
      tr := fun _ inp _ => match inp with
        | some a => ⟨.pos, fun j => j.elim0, some a, some ()⟩
        | none => ⟨0, fun j => j.elim0, some b, none⟩ }

/-- Before the right blank, exactly the scanned prefix has been emitted.
**Proof sketch.** Induct over the input positions. Every nonblank transition
copies its bit and advances once; the emitting halt is still ahead. -/
private lemma emitterAppend_run (b : Bool) (x : List Bool) :
    ∀ j (hj : j ≤ x.length),
      (appendBitTM b).tm.runFrom ((appendBitTM b).tm.initCfg x) j =
        scanCfg x (some ()) j hj (x.take j) := by
  intro j
  induction j with
  | zero =>
    intro hj
    apply Cfg.ext_zero_tapes <;> simp [scanCfg, appendBitTM]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    unfold MultiTapeTM.step
    change ((appendBitTM b).tm.tr ()
      (scanCfg x (some ()) j (by omega) (x.take j)).inputSymbol _).apply _ = _
    rw [scanCfg_read, List.getElem?_eq_getElem (by omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · exact moveInputPos_pos_of_ne_right _ (by simp [scanCfg]; omega)
    · simp only [appendBitTM, Action.apply, scanCfg, Option.toList_some,
        List.take_succ, List.getElem?_eq_getElem (by omega : j < x.length)]

/-- **The bit appender's time**. On every input `x` the appender halts within `|x| + 1` steps with
output `x ++ [b]`.

**Proof sketch.** The body of today's `computesFunInTime_appendBit`: the private copy invariant
`emitterAppend_run` holds for `|x|` steps, and the next step reads the blank, emits `b` and halts.
-/
theorem appendBitTM_computes (b : Bool) (x : List Bool) :
    (appendBitTM b).ComputesInTime x (x ++ [b]) (x.length + 1) := by
  sorry

/-- **P18′, append one bit** (design §11, narrowed at
spec time from the drafted accumulator row: cross-round persistence is the
loop engine's state-word mechanism, so the catalog atom is just the
append; customers: fresh-variable counters in 3B-cont and 4A, via the
loop state word). Append a single fixed bit to the input word, in linear
time.

**Construction sketch.** Copy the input verbatim, emit `b`, halt — P1's
copier with one extra emission on the halting transition. -/
theorem computesFunInTime_appendBit (b : Bool) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => x ++ [b]) fun n => c * (n + 1) := by
  refine ⟨appendBitTM b, 1, fun x => ?_⟩
  apply (FinTM.computesInTime_iff _ _ _ _).mpr
  simp only [one_mul]
  rw [MultiTapeTM.runFrom_succ_eq_step', emitterAppend_run b x x.length (by omega)]
  unfold MultiTapeTM.step
  change let d := ((appendBitTM b).tm.tr ()
    (scanCfg x (some ()) x.length (by omega) (x.take x.length)).inputSymbol _).apply _
    d.Halted ∧ d.output = x ++ [b]
  rw [scanCfg_read]
  simp [appendBitTM, scanCfg, Action.apply, Cfg.Halted]

end Turing.FinTM

## ===== TCSlib/Complexity/TuringMachine/Build/WordTiming.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.TuringMachine.Build.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Time bounds for concatenating computed words

The outputs of two computations on the same input can be concatenated with a bound proportional to their separate running times and the input length. The construction uses paired storage and the timed payload-map contract.

## Main definitions

None.

## Main results

* `Turing.FinTM.exists_append_computesFunInTime` gives the additive running-time bound.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2, multitape machines, and §7.2, efficient arithmetic.)
-/

namespace Turing.FinTM

attribute [local irreducible] FinTM.ComputesFunInTime FinTM.ComputesInTime
attribute [local irreducible] pairEncode pairDecode bufferedCompTM

/-- Two computations on the same input can have their outputs concatenated with
linear overhead in their separate time bounds and the input length.

**Proof sketch.** Duplicate the input and map the first computation over the payload.
Duplicate the resulting pair, then compute the second result from its original-input
projection. Concatenate and remove the retained input. Each call is charged at its
actual input, and the two computed words have length at most their run times. -/
theorem exists_append_computesFunInTime {F G : FinTM Bool}
    {f g : List Bool → List Bool} {A B : ℕ → ℕ}
    (hf : F.ComputesFunInTime f A) (hg : G.ComputesFunInTime g B) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => f x ++ g x)
        (fun n => c * (A n + B n + n + 1)) := by
  obtain ⟨D, a, hD⟩ := computesFunInTime_pairDup
  obtain ⟨P, hP⟩ := exists_pairMapSnd_computesInTime F
  let G' := bufferedCompTM (pairExtractTM true false) G
  obtain ⟨Q, hQ⟩ := exists_pairMapSnd_computesInTime G'
  let C := pairExtractTM true true
  let S := pairExtractTM false true
  let M := bufferedCompTM
    (bufferedCompTM (bufferedCompTM (bufferedCompTM (bufferedCompTM D P) D) Q) C) S
  refine ⟨M, 4 * a + 1500, (computesFunInTime_iff _ _ _).2 fun x => ?_⟩
  let n := x.length
  let budget := A n + B n + n + 1
  let p := pairEncode x x
  let s := pairEncode x (f x)
  let q := pairEncode s s
  let r := pairEncode s (g x)
  have hf' := (computesFunInTime_iff _ _ _).1 hf x
  have hg' := (computesFunInTime_iff _ _ _).1 hg x
  have hlf : (f x).length ≤ A n := by
    rw [← ((computesInTime_iff _ _ _ _).1 hf').2]
    exact F.tm.output_length_le x _
  have hlg : (g x).length ≤ B n := by
    rw [← ((computesInTime_iff _ _ _ _).1 hg').2]
    exact G.tm.output_length_le x _
  have h₁ := (computesFunInTime_iff _ _ _).1 hD x
  have h₂ := hP x x (f x) (A n) hf'
  have h₃ := (computesFunInTime_iff _ _ _).1 hD s
  have hproj : (pairExtractTM true false).ComputesInTime s x (5 * (s.length + 1)) := by
    simpa only [s, pairDecode_pairEncode, Bool.false_eq_true, ↓reduceIte, List.append_nil] using
      pairExtractTM_computes true false s
  have hrun : G'.ComputesInTime s (g x) (5 * (s.length + 1) + n + 2 + B n) :=
    bufferedCompTM_computesInTime (pairExtractTM true false) G hproj hg'
  have h₄ := hQ s s (g x) _ hrun
  have h₅ : C.ComputesInTime r (s ++ g x) (5 * (r.length + 1)) := by
    simpa only [C, r, pairDecode_pairEncode, ↓reduceIte] using
      pairExtractTM_computes true true r
  have hword : s ++ g x = pairEncode x (f x ++ g x) := by
    simp only [s, pairEncode_eq, List.append_assoc]
  have h₆ : S.ComputesInTime (s ++ g x) (f x ++ g x) (5 * ((s ++ g x).length + 1)) := by
    rw [hword]
    simpa only [S, pairDecode_pairEncode, ↓reduceIte, List.nil_append] using
      pairExtractTM_computes false true (pairEncode x (f x ++ g x))
  have h := bufferedCompTM_computesInTime D P h₁ h₂
  have h := bufferedCompTM_computesInTime _ D h h₃
  have h := bufferedCompTM_computesInTime _ Q h h₄
  have h := bufferedCompTM_computesInTime _ C h h₅
  have h := bufferedCompTM_computesInTime _ S h h₆
  have hn : n + 1 ≤ budget := by dsimp only [budget]; omega
  have hs : s.length ≤ 2 * budget := by
    rw [show s = pairEncode x (f x) from rfl, length_pairEncode]
    dsimp only [budget, n] at hlf ⊢
    omega
  have hsmall : 1 ≤ budget := by omega
  have hp : p.length ≤ 3 * budget := by
    rw [show p = pairEncode x x from rfl, length_pairEncode]
    dsimp only [n] at hn
    omega
  have hq : q.length ≤ 8 * budget := by
    rw [show q = pairEncode s s from rfl, length_pairEncode]
    omega
  have hr : r.length ≤ 7 * budget := by
    rw [show r = pairEncode s (g x) from rfl, length_pairEncode]
    have : B n ≤ budget := by dsimp only [budget]; omega
    omega
  have hd₁ : a * (n + 1) ≤ a * budget := Nat.mul_le_mul_left _ hn
  have hd₂ : a * (s.length + 1) ≤ a * (3 * budget) :=
    Nat.mul_le_mul_left _ (by omega)
  have hA : A n ≤ budget := by dsimp only [budget]; omega
  have hB : B n ≤ budget := by dsimp only [budget]; omega
  refine h.mono ?_
  have hbound : (4 * a + 1500) * budget = a * budget + a * (3 * budget) + 1500 * budget := by
    ring
  change _ ≤ (4 * a + 1500) * budget
  rw [hbound]
  rw [List.length_append]
  change a * (n + 1) + p.length + 2 + 40 * (A n + p.length + 1) +
    s.length + 2 + a * (s.length + 1) +
    q.length + 2 + 40 * (5 * (s.length + 1) + n + 2 + B n + q.length + 1) +
    r.length + 2 + 5 * (r.length + 1) +
    (s.length + (g x).length) + 2 + 5 * (s.length + (g x).length + 1) ≤ _
  omega


end Turing.FinTM

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
  `TCSlib.Cryptography.Asymptotic.UniversalPadding`, with its linear-time evaluator).
* `TCSlib.Cryptography.claim_65_1`, `claim_65_2`, `claim_65_2_cond` — `PickG` and the union
  bound [PS10, p. 65].
* `TCSlib.Cryptography.fUniversal_hard`, `TCSlib.Cryptography.fUniversal_weakOneWay`,
  `TCSlib.Cryptography.theorem_63_1` — `f_universal` is weakly one-way with `q(n) = n³`, hence
  (after amplification) strongly one-way [PS10, Theorem 63.1] (`fUniversal_hard` and
  `fUniversal_weakOneWay` are proved from the hypothesis of `lemma_64_3`; `theorem_63_1`
  uses the quadratic-time strong one-way family supplied by `lemma_64_3`).

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

/-- The input length of `fUniversal c` at `n` is `n`. -/
theorem fUniversal_inLen_eval (c : EffectiveMachineCode) (n : ℕ) :
    (fUniversal c).inLen.eval n = n :=
  FunFamily.ofString_inLen_eval _ _ n

/-- The padded reading of a string: `List.ofFn (fun i : Fin p => w.getD i false)` is
`(w ++ 0^p).take p` (the encoding of `FunFamily.ofString`'s output). -/
theorem ofFn_getD_eq_take (w : List Bool) (p : ℕ) :
    List.ofFn (fun i : Fin p => w.getD i false) = (w ++ List.replicate p false).take p :=
  ofFn_padFin_eq_take p w

/-- The encoding of `fUniversal c` at parameter `n` is the string output padded with `false`
to `univOutLen n` bits. -/
theorem ofFn_fUniversal_f (c : EffectiveMachineCode) (n : ℕ)
    (x : Fin ((fUniversal c).inLen.eval n) → Bool) :
    List.ofFn ((fUniversal c).f n x) =
      (fUniversalStr c (List.ofFn x) ++ List.replicate (univOutLen.eval n) false).take
        (univOutLen.eval n) := by
  refine (List.ofFn_congr (FunFamily.ofString_outLen_eval (fUniversalStr c) univOutLen n) _).trans
    (Eq.trans ?_ (ofFn_getD_eq_take _ _))
  exact congrArg List.ofFn
    (funext fun i => (FunFamily.ofString_f_apply _ _ n x _).trans (by rw [Fin.coe_cast]))

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
  simp only [univCoeff, universalBlockBound_def]
  omega

/-! ## The evaluator machine of `f_universal` -/

/-- **The code field is polynomial-time**: the typed cut `polyTimeComputable_pairTakePoly var`
on `⟨(bits |y|).tail, y⟩` keeps the first `⌊log₂ |y|⌋` bits (`length_tail_bits`). -/
theorem polyTimeComputable_univCode : PolyTimeComputable univCode := by
  have h := PolyTimeComputable.comp' (polyTimeComputable_pairTakePoly .var)
    (polyTimeComputable_logMarker.pairEncode polyTimeComputable_id)
  convert h using 1
  funext y
  simp only [univCode, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var, id_eq,
    length_tail_bits]

/-- **The argument field is polynomial-time**: the typed cut `polyTimeComputable_pairDropPoly var`
on `⟨(bits |y|).tail, y⟩` drops the first `⌊log₂ |y|⌋` bits (`length_tail_bits`). -/
theorem polyTimeComputable_univArg : PolyTimeComputable univArg := by
  have h := PolyTimeComputable.comp' (polyTimeComputable_pairDropPoly .var)
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
  obtain ⟨M, C, d, hM⟩ := (polyTimeComputable_iff _).1 polyTimeComputable_univInput
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
  refine (polyTimeComputable_iff _).2 ⟨N, C', c', (FinTM.computesFunInTime_iff _ _ _).2 fun y =>
    ((FinTM.computesFunInTime_iff _ _ _).1 hN y).mono ?_⟩
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
    have h := PolyTimeComputable.comp' (polyTimeComputable_padStr univOutLen)
      (polyTimeComputable_pairFstD.pairEncode
        (PolyTimeComputable.comp' (polyTimeComputable_fUniversalStr c hc)
            polyTimeComputable_pairSndD))
    convert h using 1
    funext z
    simp
  refine (FunFamily.easy_iff _).2 ⟨_, hF, fun n x => ?_⟩
  simp only [NUPPT.advInput_eq, pairFstD_pairEncode, pairSndD_pairEncode]
  rw [ofFn_fUniversal_f]
  simp [padStr_eq]

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
with `ν(m) := max {n ≤ m : n^d ≤ m}` recovered from the input length for a fixed
dominating degree d. The output `a ++ g_{ν m}(b)` is padded with `false` to the syntactic
length `2·var` and is truncated on smaller parameters before domination applies.

Repair (run-3 audit P3-3): the sketch's family is `𝓖 := ⟨var, mul (const 2) var, g'⟩`, not
`⟨var, add var outLen, g'⟩` — padding to `m + outLen(m)` bits is not computable within the
quadratic one-tape budget when `deg outLen ≥ 2`; the raw output has at most `2m` bits. The
"non-constant input length" sub-lemma is unnecessary (`P` is strictly increasing because of its
summand `n`). Statement unchanged.

**Proof sketch.** Extract an evaluator F of the strong one-way family and
its polynomial running time. Choose a fixed degree d that eventually dominates
the input length, output length and the cost of F on an encoded parameter
and input. The family PadQuad.family uses the recovered parameter
ν(m) = max {n ≤ m : n^d ≤ m}. Its output is the retained suffix followed by
F on the encoded parameter and data prefix, padded and truncated to twice m.

The padding inverter samples the retained suffix and uses the supplied
padded-family inverter at a length selected as advice. Equality of padded
outputs gives equality of the retained suffix and equality of the original
family's outputs once the dominating bound holds. This proves the padded
family's strong one-wayness.

For time, the binary parameter search followed by unary emission computes
the shifted root in linear multitape time. The sharp unary polynomial
evaluator and the source call are charged at their actual short arguments.
The pairing, splitting and padding stages have linear overhead. The existing
one-work-tape binary conversion squares that linear bound, and the code
representation transports the runs. This is PadQuad.exists_family.
-/
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
  rw [uprob_prod, uexp_def]
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
    (hc₀ : c₀ ≤ n + 1) (x : Fin (n - Nat.log 2 n) → Bool)
    (y : Fin ((fUniversal c).inLen.eval n) → Bool) (hy : List.ofFn y = code ++ List.ofFn x) :
    padStr univOutLen (List.replicate n true) (pairEncode code (true :: List.ofFn (g _ x))) =
      List.ofFn ((fUniversal c).f n y) := by
  obtain ⟨y₀, hy₀⟩ := exists_ofFn_eq_of_length (m := n) (w := List.ofFn y)
    (by rw [List.length_ofFn, fUniversal_inLen_eval])
  rw [ofFn_fUniversal_f, ← hy₀,
    fUniversalStr_ofFn_eq c g Mg c₀ hMg hcode hdec hc₀ x y₀ (hy₀.trans hy), padStr_eq,
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
    (hc₀ : c₀ ≤ n + 1) (x : Fin (n - Nat.log 2 n) → Bool)
    (y y' : Fin ((fUniversal c).inLen.eval n) → Bool)
    (hy : List.ofFn y = code ++ List.ofFn x) (h : (fUniversal c).f n y' = (fUniversal c).f n y) :
    ∃ x' : Fin (n - Nat.log 2 n) → Bool, List.ofFn x' = univArg (List.ofFn y') ∧ g _ x' = g _ x := by
  have hkn : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
  obtain ⟨x', hx'⟩ := exists_ofFn_eq_of_length (m := n - Nat.log 2 n)
    (w := univArg (List.ofFn y')) (by simp [fUniversal_inLen_eval])
  refine ⟨x', hx', ?_⟩
  obtain ⟨y₀, hy₀⟩ := exists_ofFn_eq_of_length (m := n) (w := List.ofFn y)
    (by rw [List.length_ofFn, fUniversal_inLen_eval])
  have h1 := congrArg List.ofFn h
  rw [ofFn_fUniversal_f, ofFn_fUniversal_f,
    take_append_replicate_of_le
      (by simpa [fUniversal_inLen_eval] using length_fUniversalStr_le c (List.ofFn y')),
    take_append_replicate_of_le
      (by simpa [fUniversal_inLen_eval] using length_fUniversalStr_le c (List.ofFn y)),
    ← hy₀, fUniversalStr_ofFn_eq c g Mg c₀ hMg hcode hdec hc₀ x y₀ (hy₀.trans hy)] at h1
  unfold fUniversalStr at h1
  simp only [List.length_ofFn] at h1
  rw [show ((fUniversal c).inLen.eval n + 1) ^ 3 = (n + 1) ^ 3 by rw [fUniversal_inLen_eval]] at h1
  obtain ⟨hcd, hans⟩ := pairEncode_append_eq (by simp [hcode, fUniversal_inLen_eval]) h1
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
    have h := PolyTimeComputable.comp' (polyTimeComputable_padStr univOutLen)
      ((PolyTimeComputable.comp' polyTimeComputable_pairFstD polyTimeComputable_pairFstD).pairEncode
        ((PolyTimeComputable.comp' polyTimeComputable_pairSndD
            polyTimeComputable_pairFstD).pairEncode
          (PolyTimeComputable.comp' (StateLoop.cons_poly true) polyTimeComputable_pairSndD)))
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
    simp only [NUPPT.coinLen_eq, hBc, PolyExpr.eval_subst]
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

## ===== TCSlib/Cryptography/Asymptotic/UniversalPadding.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Cryptography.Asymptotic.Collections
import TCSlib.Cryptography.Asymptotic.UniversalLemmas
import TCSlib.Cryptography.Asymptotic.UniversalPadding.Parameter
import TCSlib.Cryptography.Asymptotic.UniversalPadding.BinaryRoot
import TCSlib.Cryptography.Asymptotic.UniversalPadding.Machine

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
[Gar26, Lemma 2.3]); a linear-time multitape evaluator (`PadQuad.exists_linearTime_gStr`) gives a quadratic-time one-work-tape binary machine through
`Turing.FinTM.one_work_tape_binary` and `Turing.exists_codeTM` (`PadQuad.quadraticCode_of_linear`).

**Deviation:** the text defines `g'` on lengths `m = n^c` only; here every length `m` is
handled through `ν` (data first, padding after, zero-filled to `2m` bits), see the docstring of
`TCSlib.Cryptography.lemma_64_3`.

## Contents

* `UniversalPadding.Parameter` — the recovered parameter and its bounds.
* `UniversalPadding.BinaryRoot` — the binary computation of the shifted parameter.
* `UniversalPadding.Machine` — the linear-time word evaluator.

## Main definitions

* `TCSlib.Cryptography.PadQuad.nu` — the parameter recovered from the input length;
  `TCSlib.Cryptography.PadQuad.raw`, `PadQuad.gStr`, `PadQuad.family` — the padded function.

## Main results

* `TCSlib.Cryptography.PadQuad.exists_pow_dominates` — `p(n) ≤ n^d` eventually.
* `TCSlib.Cryptography.PadQuad.easy_of_linear`, `PadQuad.quadraticCode_of_linear` — the two
  computability clauses from the linear-time evaluator.
* `TCSlib.Cryptography.PadQuad.exists_linearTime_gStr` — the linear-time evaluator.
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

/-! ## Polynomial domination -/

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
    (x : Fin ((family F ℓ d).inLen.eval m) → Bool) :
    List.ofFn ((family F ℓ d).f m x) = gStr F ℓ d (List.ofFn x) :=
  FunFamily.ofFn_ofString_apply (lengthRegular_gStr F ℓ d) m x

/-! ## The computability clauses -/

/-- The padded family has a linear-time multitape evaluator.
[PS10, Lemma 64.3, the quadratic-time computation of the padded function]
Given a machine for F within C (k + 1)^c and a fixed degree dominating the
data length and the call cost, the evaluator computes gStr in linear time.

**Proof sketch.** Compute the input length in binary and recover the shifted
root by interval halving. At degree one, a single transducer suffices.
At larger degrees, the emitting loop converts the canonical binary root
to unary within a quadratic bound in the root, which fits the input length.
Evaluate the syntactic length polynomial on the shifted unary word using
the sharp monomial emitter. Restore the root's token and split the data.
The timed payload map retains the suffix while applying F to its actual
encoded argument. Concatenate the suffix, result and zeros, and cut to
twice the input length. The image bounds cover every length, including
the empty word and parameters below the domination threshold. -/
theorem exists_linearTime_gStr {F : List Bool → List Bool} {M : FinTM Bool} {C c : ℕ}
    (hM : M.ComputesFunInTime F fun k => C * (k + 1) ^ c) (ℓ : PolyExpr) {d n₁ : ℕ}
    (hd : 1 ≤ d) (hdom : ∀ n ≥ n₁, ℓ.eval n + C * (2 * n + 3 + ℓ.eval n) ^ c ≤ n ^ d) :
    ∃ (M' : FinTM Bool) (c' : ℕ), M'.ComputesFunInTime (gStr F ℓ d) fun m => c' * (m + 1) := by
  simpa only [gStr, raw] using exists_linearTime_padded hM ℓ hd hdom

/-- **`g'` is easy to compute** from a linear-time evaluator: the evaluator on `⟨1^m, y⟩`
applies `gStr` to the second component (`ofFn_family_f`). -/
theorem easy_of_linear {F : List Bool → List Bool} {ℓ : PolyExpr} {d : ℕ}
    (h : ∃ (M' : FinTM Bool) (c' : ℕ), M'.ComputesFunInTime (gStr F ℓ d) fun m => c' * (m + 1)) :
    (family F ℓ d).Easy := by
  have hg : PolyTimeComputable (gStr F ℓ d) := polyTimeComputable_of_linear h
  refine (FunFamily.easy_iff _).2
    ⟨fun z => gStr F ℓ d (pairSndD z), hg.comp polyTimeComputable_pairSndD, fun m x => ?_⟩
  rw [ofFn_family_f, NUPPT.advInput_eq]
  exact congrArg (gStr F ℓ d) (pairSndD_pairEncode _ _)

/-- **`g'` is computable by a coded machine in quadratic time** from a linear-time multitape
evaluator: `Turing.FinTM.one_work_tape_binary` gives a one-work-tape binary machine within
`c₁ (c' (m + 1) + 1)² ≤ c₁ (c' + 1)² (m + 1)²`, and `Turing.exists_codeTM` a `CodeTM` with the
same runs. -/
theorem quadraticCode_of_linear {F : List Bool → List Bool} {ℓ : PolyExpr} {d : ℕ}
    (h : ∃ (M' : FinTM Bool) (c' : ℕ), M'.ComputesFunInTime (gStr F ℓ d) fun m => c' * (m + 1)) :
    ∃ (Mc : CodeTM) (c₀ : ℕ), ∀ m (x : Fin ((family F ℓ d).inLen.eval m) → Bool),
      Mc.toFinTM.ComputesInTime (List.ofFn x) (List.ofFn ((family F ℓ d).f m x))
        (c₀ * (m + 1) ^ 2) := by
  obtain ⟨M', c', hM'⟩ := h
  obtain ⟨M₁, c₁, hk, hM₁⟩ := FinTM.one_work_tape_binary M' _ _ hM'
  obtain ⟨Mc, hMc⟩ := exists_codeTM M₁ hk
  refine ⟨Mc, c₁ * (c' + 1) ^ 2, fun m x => ?_⟩
  rw [ofFn_family_f, hMc]
  refine ((FinTM.computesFunInTime_iff _ _ _).1 hM₁ (List.ofFn x)).mono ?_
  rw [List.length_ofFn, family_inLen, PolyExpr.eval_var]
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
  unfold gStr
  simp only [padStr_eq]
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
    simp [NUPPT.coinLen_eq, hAc, PolyExpr.eval_subst]
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
    obtain ⟨n₀, hn₀⟩ := (negligible_iff _).1 (h.hard A) (d * e + 1)
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
`ℓ + L + (running time of the evaluator)`, using its linear-time evaluator
(`exists_linearTime_gStr`).

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
  obtain ⟨F, hF, hFx⟩ := (FunFamily.easy_iff 𝓕).1 h.easy
  obtain ⟨M, C, c, hM⟩ := (polyTimeComputable_iff F).1 hF
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

## ===== TCSlib/Cryptography/Asymptotic/UniversalPadding/BinaryRoot.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.ClassP.BinaryArith.Unary
import TCSlib.Cryptography.Asymptotic.UniversalPadding.Parameter

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The binary floor-root computation for Levin padding

A guarded word iteration bisects an interval containing the recovered parameter. Its state has linear binary width, and every round uses the shared binary arithmetic interface.

## Main definitions

The private search state retains the normalized argument, a word whose length counts the remaining rounds, and the lower endpoint.

## Main results

* `TCSlib.Cryptography.PadQuad.polyTimeComputable_shifted_root` computes the canonical binary word of the recovered parameter minus one.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010. (§2.13, Lemma 64.3.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2, multitape machines, and §7.2, efficient arithmetic.)
-/

open Turing Complexity Complexity.BinArith TCSlib.Cryptography Complexity.LogProg

attribute [local irreducible] PadQuad.nu pairEncode pairFstD pairSndD
attribute [local irreducible] BinArith.add BinArith.sub BinArith.mul BinArith.le
attribute [local irreducible] transduce PolyTimeComputable

namespace TCSlib.Cryptography.PadQuad

/-- Any fixed power of a binary input is computable in polynomial time by repeated
binary multiplication, with both factors normalized at every call. -/
private theorem polyTimeComputable_fixedPower (d : ℕ) :
    PolyTimeComputable (fun z => Nat.bits (bitsVal z ^ d)) := by
  induction d with
  | zero => simpa only [pow_zero] using polyTimeComputable_const (Nat.bits 1)
  | succ d ih =>
      convert polyTimeComputable_mul.comp (ih.pairEncode polyTimeComputable_normBits) using 1
      funext z
      simp only [Function.comp_apply, mul_pairEncode, pow_succ]

/-- The initialization retains the normalized input, its original length as
remaining rounds, and the lower endpoint zero. -/
private def init (z : List Bool) : List Bool :=
  pairEncode (Nat.bits (bitsVal z)) (pairEncode z (Nat.bits 0))

/-- On a state with unread tokens, the midpoint of the search interval
adds the power of two indexed by the remaining length after this round. -/
private def midpoint (s : List Bool) : List Bool :=
  BinArith.add (pairEncode (pairSndD (pairSndD s))
    (Nat.bits (2 ^ ((pairFstD (pairSndD s)).drop 1).length)))

/-- Compare the midpoint's fixed power with the input. The accepted lower
endpoint is retained as a binary word, and the remaining width decreases by one. -/
private def round (d : ℕ) (s : List Bool) : List Bool :=
  if pairFstD (pairSndD s) = [] then s
  else
    let cand := midpoint s
    let test := BinArith.le
      (pairEncode (Nat.bits (bitsVal cand ^ d)) (pairFstD s))
    pairEncode (pairFstD s)
      (pairEncode ((pairFstD (pairSndD s)).drop 1)
        (if test then cand else pairSndD (pairSndD s)))

/-- Each search round is polynomial-time by the word projections and the
binary addition, multiplication and comparison interfaces. -/
private theorem polyTimeComputable_round (d : ℕ) : PolyTimeComputable (round d) := by
  have htail : PolyTimeComputable (fun s => (pairFstD (pairSndD s)).drop 1) :=
    polyTimeComputable_drop 1 |>.comp polyTimeComputable_slot2
  have hmid : PolyTimeComputable midpoint :=
    polyTimeComputable_add.comp
      (polyTimeComputable_slot3.pairEncode (polyTimeComputable_powerOfTwo.comp htail))
  have htest := polyTimeComputable_le.comp
    (((polyTimeComputable_fixedPower d).comp hmid).pairEncode polyTimeComputable_pairFstD)
  have hupdate := polyTimeComputable_ite htest hmid polyTimeComputable_slot3
  have hbranch := polyTimeComputable_ite
    (polyTimeComputable_isNil.comp polyTimeComputable_slot2) polyTimeComputable_id
    (polyTimeComputable_pairFstD.pairEncode (htail.pairEncode hupdate))
  simpa only [Function.comp_apply, round, decide_eq_true_eq] using hbranch

/-- The true root lies in the half-open interval of width two to the number
of remaining rounds, with the original normalized argument retained. -/
private def Invariant (d : ℕ) (z s : List Bool) : Prop :=
  ∃ (u : List Bool) (r : ℕ),
    s = pairEncode (Nat.bits (bitsVal z)) (pairEncode u (Nat.bits r)) ∧
      u.length ≤ z.length ∧ r ≤ PadQuad.nu d (bitsVal z) ∧
      PadQuad.nu d (bitsVal z) < r + 2 ^ u.length

/-- The full binary width covers every possible root of the input. -/
private theorem invariant_init (d : ℕ) (z : List Bool) : Invariant d z (init z) := by
  refine ⟨z, 0, rfl, le_rfl, Nat.zero_le _, ?_⟩
  rw [Nat.zero_add]
  exact (PadQuad.nu_le _ _).trans_lt (bitsVal_lt_two_pow z)

/-- A nonempty round splits the invariant interval into equal halves. The
midpoint's power is within the original value exactly when the midpoint is at
most the root. The remaining word loses one letter. An empty round is fixed. -/
private theorem invariant_round {d : ℕ} (hd : 1 ≤ d) {z s : List Bool}
    (hs : Invariant d z s) : Invariant d z (round d s) ∧
      (0 < (pairFstD (pairSndD s)).length →
        (pairFstD (pairSndD (round d s))).length < (pairFstD (pairSndD s)).length) ∧
      ((pairFstD (pairSndD s)).length = 0 → round d s = s) := by
  obtain ⟨u, r, rfl, hlu, hlow, hhigh⟩ := hs
  cases u with
  | nil =>
      simp only [round, pairFstD_pairEncode, pairSndD_pairEncode, ↓reduceIte,
        List.length_nil, Nat.lt_irrefl, false_implies, true_implies, and_true]
      exact ⟨[], r, rfl, hlu, hlow, hhigh⟩
  | cons b u =>
      let v := PadQuad.nu d (bitsVal z)
      let k := 2 ^ u.length
      have htest : (r + k) ^ d ≤ bitsVal z ↔ r + k ≤ v :=
        ⟨PadQuad.le_nu hd, fun h => (Nat.pow_le_pow_left h _).trans (PadQuad.nu_pow_le hd _)⟩
      have hwidth : 2 ^ (b :: u).length = k + k := by
        simp only [List.length_cons, pow_succ, k, Nat.mul_two]
      rw [hwidth] at hhigh
      have hr :
          round d (pairEncode (Nat.bits (bitsVal z)) (pairEncode (b :: u) (Nat.bits r))) =
            pairEncode (Nat.bits (bitsVal z))
              (pairEncode u (Nat.bits (if r + k ≤ v then r + k else r))) := by
        simp only [round, pairFstD_pairEncode, pairSndD_pairEncode, List.cons_ne_nil,
          ↓reduceIte, midpoint, List.drop_succ_cons, List.drop_zero, add_pairEncode,
          bitsVal_bits, le_pairEncode, decide_eq_true_eq]
        change pairEncode (Nat.bits (bitsVal z))
          (pairEncode u (if (r + k) ^ d ≤ bitsVal z then Nat.bits (r + k) else Nat.bits r)) = _
        by_cases h : r + k ≤ v
        · rw [if_pos (htest.mpr h), if_pos h]
        · rw [if_neg (fun h' => h (htest.mp h')), if_neg h]
      rw [hr]
      refine ⟨?_, ?_, ?_⟩
      · have hu : u.length ≤ z.length := by simp only [List.length_cons] at hlu; omega
        by_cases h : r + k ≤ v
        · refine ⟨u, r + k, by rw [if_pos h], hu, h, ?_⟩
          change v < r + k + k
          omega
        · exact ⟨u, r, by rw [if_neg h], hu, hlow, by exact Nat.lt_of_not_ge h⟩
      · simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_cons]
        omega
      · simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_cons]
        omega

/-- The interval representation is linear in the original binary width.
The lower endpoint fits because it is at most the root of the input. -/
private theorem length_le_of_invariant {d : ℕ} {z s : List Bool} (h : Invariant d z s) :
    s.length ≤ 5 * (z.length + 1) := by
  obtain ⟨u, r, rfl, hu, hr, -⟩ := h
  have hn := length_bits_bitsVal_le z
  have hl := length_bits_le_of_le z (hr.trans (PadQuad.nu_le _ _)) le_rfl
  simp only [length_pairEncode]
  omega

/-- The binary root can be computed in time polynomial in the binary input
width. The truncated subtraction produces the shifted root used by the
sharp unary polynomial evaluator.

**Proof sketch.** Reuse the guarded word loop with the interval round. The
lower endpoint is never above the root, and the interval halves at every
round until the remaining word is empty. The final interval has width one.
Project the lower endpoint and subtract one. -/
theorem polyTimeComputable_shifted_root (d : ℕ) (hd : 1 ≤ d) :
    PolyTimeComputable (fun z => Nat.bits (PadQuad.nu d (bitsVal z) - 1)) := by
  let loops (z : List Bool) := (round d)^[z.length + 1] (init z)
  have hinit : PolyTimeComputable init :=
    polyTimeComputable_normBits.pairEncode
      (polyTimeComputable_id.pairEncode (polyTimeComputable_const _))
  have hpreserve : ∀ (z s : List Bool), Invariant d z s → Invariant d z (round d s) :=
    fun _ _ h => (invariant_round hd h).1
  have hloops : PolyTimeComputable loops := by
    simpa only [pow_one, one_mul] using
      BinArith.polyTimeComputable_iterate (polyTimeComputable_round d) hinit 1 1 5 1
        (fun z i _ => by simpa only [pow_one] using
          length_le_of_invariant (iterate_invariant (Invariant d z) (hpreserve z) i
            (invariant_init d z)))
  have hresult (z : List Bool) :
      pairSndD (pairSndD (loops z)) = Nat.bits (PadQuad.nu d (bitsVal z)) := by
    have hzero := iterate_measure_eq_zero (g := round d) (Invariant d z)
      (fun s => (pairFstD (pairSndD s)).length) (hpreserve z)
      (fun _ h => (invariant_round hd h).2.1)
      (fun _ h => (invariant_round hd h).2.2) (z.length + 1) (init z)
      (invariant_init d z) (by simp only [init, pairFstD_pairEncode, pairSndD_pairEncode]; omega)
    change (pairFstD (pairSndD (loops z))).length = 0 at hzero
    obtain ⟨u, r, hword, -, hlow, hhigh⟩ :=
      iterate_invariant (Invariant d z) (hpreserve z) (z.length + 1) (invariant_init d z)
    change loops z = _ at hword
    rw [hword] at hzero ⊢
    simp only [pairFstD_pairEncode, pairSndD_pairEncode] at hzero ⊢
    rw [hzero, pow_zero] at hhigh
    congr 1
    omega
  have hsub := polyTimeComputable_sub.comp
    ((polyTimeComputable_slot3.comp hloops).pairEncode (polyTimeComputable_const (Nat.bits 1)))
  convert hsub using 1
  funext z
  simp only [Function.comp_apply, hresult, sub_pairEncode]


end TCSlib.Cryptography.PadQuad

## ===== TCSlib/Cryptography/Asymptotic/UniversalPadding/Machine.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.UniversalPadding.BinaryRoot
import TCSlib.Complexity.Randomized.UnaryPolynomial
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Complexity.ClassNP.Transducer
import TCSlib.Complexity.Randomized.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The linear-time multitape evaluator of Levin padding

The evaluator computes the shifted unary root, the unary data length, the source call and the padded result. Both polynomial computations are charged at their actual short arguments. Finite small inputs are absorbed into the running-time constant.

## Main definitions

The private linear-time predicate packages a multitape evaluator and its bound. Its closures use the existing timed machine combinators.

## Main results

* `TCSlib.Cryptography.PadQuad.exists_linearTime_padded` computes the padded word formula in linear time.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010. (§2.13, Lemma 64.3.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2, multitape machines, and §7.2, efficient arithmetic.)
-/

open Complexity Turing Turing.FinTM TCSlib.Cryptography Complexity.LogProg Complexity.BinArith

attribute [local irreducible] FinTM.ComputesFunInTime FinTM.ComputesInTime
attribute [local irreducible] PolyTimeComputable PadQuad.nu NUPPT.advInput
attribute [local irreducible] pairEncode pairDecode pairFstD pairSndD transduce

namespace TCSlib.Cryptography.PadQuad

/-- At the recovered parameter, the unary data length and the time of the call
to the original machine fit a linear budget in the padded input length. -/
private theorem levinTimeOnImage (ℓ : PolyExpr) (C c d n₁ : ℕ) (hd : 1 ≤ d)
    (hdom : ∀ n ≥ n₁, ℓ.eval n + C * (2 * n + 3 + ℓ.eval n) ^ c ≤ n ^ d) :
    ∃ B : ℕ, ∀ z : List Bool,
      let n := PadQuad.nu d z.length
      ℓ.eval n + C * ((NUPPT.advInput n (z.take (ℓ.eval n))).length + 1) ^ c ≤
        B * (z.length + 1) := by
  let B := ℓ.eval n₁ + C * (2 * n₁ + 3 + ℓ.eval n₁) ^ c + 1
  refine ⟨B, fun z => ?_⟩
  let n := PadQuad.nu d z.length
  change ℓ.eval n + C * ((NUPPT.advInput n (z.take (ℓ.eval n))).length + 1) ^ c ≤
    B * (z.length + 1)
  have hinput : (NUPPT.advInput n (z.take (ℓ.eval n))).length + 1 ≤
      2 * n + 3 + ℓ.eval n := by
    rw [NUPPT.length_advInput, List.length_take]
    omega
  have htime := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hinput c)
  by_cases hn : n₁ ≤ n
  · have hB : 1 ≤ B := by omega
    calc
      _ ≤ ℓ.eval n + C * (2 * n + 3 + ℓ.eval n) ^ c := Nat.add_le_add_left htime _
      _ ≤ n ^ d := hdom n hn
      _ ≤ z.length := PadQuad.nu_pow_le hd _
      _ ≤ 1 * (z.length + 1) := by omega
      _ ≤ _ := Nat.mul_le_mul_right _ hB
  · have hn' : n ≤ n₁ := by omega
    have hℓ := ℓ.eval_mono hn'
    have harg : 2 * n + 3 + ℓ.eval n ≤ 2 * n₁ + 3 + ℓ.eval n₁ := by omega
    have hcost := Nat.mul_le_mul_left C (Nat.pow_le_pow_left harg c)
    calc
      _ ≤ ℓ.eval n₁ + C * (2 * n₁ + 3 + ℓ.eval n₁) ^ c :=
        Nat.add_le_add hℓ (htime.trans hcost)
      _ ≤ B := by omega
      _ ≤ _ := by simpa only [Nat.mul_one] using
        Nat.mul_le_mul_left B (Nat.succ_le_succ (Nat.zero_le z.length))


/-- A word function has a deterministic multitape evaluator with a linear bound. -/
private def Linear (f : List Bool → List Bool) : Prop :=
  ∃ (M : FinTM Bool) (a : ℕ), M.ComputesFunInTime f (fun n => a * (n + 1))

/-- A machine for pointwise equal output computes the same function. -/
private theorem Linear.congr {f g : List Bool → List Bool} (hf : Linear f)
    (h : ∀ z, f z = g z) : Linear g := by
  rwa [← funext h]

/-- The output word fits the time bound because a step emits at most one bit. -/
private theorem length_le_time {M : FinTM Bool} {x y : List Bool} {t : ℕ}
    (h : M.ComputesInTime x y t) : y.length ≤ t := by
  rw [← ((computesInTime_iff _ _ _ _).1 h).2]
  exact M.tm.output_length_le x t

/-- Two-stage computation with both stages charged against the original input. -/
private theorem Linear.onImage {f g : List Bool → List Bool} (hf : Linear f)
    (U : FinTM Bool) (b : ℕ)
    (hU : ∀ x, U.ComputesInTime (f x) (g x) (b * (x.length + 1))) : Linear g := by
  obtain ⟨M, a, hM⟩ := hf
  obtain ⟨V, hV⟩ := exists_comp_on_image M U f g _ (fun n => b * (n + 1)) hM hU
  refine ⟨V, 2 * a + b + 2, (computesFunInTime_iff _ _ _).2 fun x => ?_⟩
  refine ((computesFunInTime_iff _ _ _).1 hV x).mono ?_
  rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc]
  have hpos : 1 ≤ x.length + 1 := by omega
  have htwo := Nat.mul_le_mul_left 2 hpos
  omega

/-- Linear-time functions compose since the first output also has linear length. -/
private theorem Linear.comp {f g : List Bool → List Bool}
    (hg : Linear g) (hf : Linear f) : Linear (fun x => g (f x)) := by
  obtain ⟨M, a, hM⟩ := hf
  obtain ⟨U, b, hU⟩ := hg
  refine Linear.onImage ⟨M, a, hM⟩ U (b * (a + 1)) fun x => ?_
  refine ((computesFunInTime_iff _ _ _).1 hU (f x)).mono ?_
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  rw [Nat.add_mul, Nat.one_mul]
  have hl := length_le_time ((computesFunInTime_iff _ _ _).1 hM x)
  omega

/-- Concatenation of two linear-time outputs is linear in the same input. -/
private theorem Linear.append {f g : List Bool → List Bool}
    (hf : Linear f) (hg : Linear g) : Linear (fun x => f x ++ g x) := by
  obtain ⟨M, a, hM⟩ := hf
  obtain ⟨U, b, hU⟩ := hg
  obtain ⟨V, c, hV⟩ := exists_append_computesFunInTime hM hU
  refine ⟨V, c * (a + b + 1), (computesFunInTime_iff _ _ _).2 fun x => ?_⟩
  apply ((computesFunInTime_iff _ _ _).1 hV x).mono
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
  omega

/-- Emit the doubled first component and separator, then the second component.
The prefix uses the timed payload map with the constant empty machine. -/
private theorem Linear.pair {f g : List Bool → List Bool} (hf : Linear f) (hg : Linear g) :
    Linear (fun x => pairEncode (f x) (g x)) := by
  have hdup : Linear (fun x => pairEncode x x) := computesFunInTime_pairDup
  obtain ⟨M, a, hM⟩ := hdup.comp hf
  obtain ⟨P, hP⟩ := exists_pairMapSnd_computesInTime (constTM [])
  have hprefix : Linear (fun x => pairEncode (f x) []) := by
    refine Linear.onImage ⟨M, a, hM⟩ P (40 * (a + 2)) fun x => ?_
    have h := hP (f x) (f x) [] 1 (constTM_computes [] (f x))
    refine h.mono ?_
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    rw [Nat.add_mul]
    have hl := length_le_time ((computesFunInTime_iff _ _ _).1 hM x)
    omega
  apply (hprefix.append hg).congr
  intro x
  simp only [pairEncode_eq, List.append_nil, List.append_assoc]

/-- The one-state copying transducer uses one input scan. -/
private theorem linear_id : Linear (fun x => x) := by
  let δ := fun (_ : Unit) (_ : Bool) => ()
  let o := fun (_ : Unit) (b : Bool) => some b
  have h : Linear (transduce δ o ()) :=
    ⟨transducerTM δ o (), 1, by
      simpa only [Nat.one_mul] using transducerTM_computes δ o ()⟩
  exact h.congr (transduce_of_copy δ o () (fun _ => rfl) (fun _ => rfl))

/-- The first projection is the published linear pair parser. -/
private theorem linear_fst : Linear pairFstD := by
  obtain ⟨M, a, hM⟩ := computesFunInTime_pairFst
  exact (show Linear _ from ⟨M, a, hM⟩).congr fun x => (pairFstD_eq x).symm

/-- The second projection is the published linear pair parser. -/
private theorem linear_snd : Linear pairSndD := by
  obtain ⟨M, a, hM⟩ := computesFunInTime_pairSnd
  exact (show Linear _ from ⟨M, a, hM⟩).congr fun x => (pairSndD_eq x).symm

/-- The unary split `Turing.pairSplitAt` is the existing randomized-computation primitive. -/
private theorem linear_split : Linear pairSplitAt := computesFunInTime_pairSplitAt

/-- A one-state transducer emits one zero per input cell. -/
private theorem linear_zeros : Linear (fun x => List.replicate x.length false) := by
  have h : Linear (transduce (fun (_ : Unit) _ => ()) (fun _ _ => some false) ()) :=
    ⟨transducerTM _ _ (), 1, by
      simpa only [Nat.one_mul] using transducerTM_computes
        (fun (_ : Unit) _ => ()) (fun _ _ => some false) ()⟩
  apply h.congr
  intro x
  induction x with
  | nil => rw [transduce_nil]; rfl
  | cons b x ih => rw [transduce_cons, ih]; rfl

/-- Two copies of the zero scan give exactly twice the input length. -/
private theorem linear_double_zeros : Linear (fun x => List.replicate (2 * x.length) false) :=
  (linear_zeros.append linear_zeros).congr fun x => by
    rw [Nat.two_mul, List.replicate_add]

/-- Prepending a true token costs one step beyond the copy scan. -/
private theorem linear_prepend_true : Linear (fun x => true :: x) :=
  ⟨prependTM [true], 2, (computesFunInTime_iff _ _ _).2 fun x => by
    refine ((computesFunInTime_iff _ _ _).1 (prependTM_computes [true]) x).mono ?_
    simp only [List.length_cons, List.length_nil]
    omega⟩

/-- A nonempty word has parameter at least one, so shifting and restoring the
unary root recovers the original parameter. -/
private theorem restored_root {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) :
    PadQuad.nu d m - 1 + 1 = PadQuad.nu d m := by
  have h := PadQuad.le_nu hd (n := 1) (by simpa only [one_pow] using hm)
  omega

/-- The charged unary length and call cost stay linear after the shift. The only
new case is the empty word, where the shifted parameter is one. -/
private theorem shifted_image_bound (ℓ : PolyExpr) {C c d n₁ : ℕ} (hd : 1 ≤ d)
    (hdom : ∀ n ≥ n₁, ℓ.eval n + C * (2 * n + 3 + ℓ.eval n) ^ c ≤ n ^ d) :
    ∃ B : ℕ, ∀ z : List Bool,
      let n := PadQuad.nu d z.length - 1 + 1
      ℓ.eval n + C * ((NUPPT.advInput n (z.take (ℓ.eval n))).length + 1) ^ c ≤
        B * (z.length + 1) := by
  obtain ⟨A, hA⟩ := levinTimeOnImage ℓ C c d n₁ hd hdom
  refine ⟨A + (ℓ.eval 1 + C * 5 ^ c), fun z => ?_⟩
  cases z with
  | nil =>
      have hn : PadQuad.nu d 0 = 0 := Nat.eq_zero_of_le_zero (PadQuad.nu_le _ _)
      simp only [List.length_nil, hn, Nat.zero_sub, Nat.zero_add, List.take_nil,
        NUPPT.length_advInput, Nat.mul_one, Nat.reduceAdd]
      omega
  | cons b z =>
      simp only [restored_root hd (by simp : 1 ≤ (b :: z).length)]
      exact (hA (b :: z)).trans (Nat.mul_le_mul_right _ (by omega))

/-- A linear-time evaluator for the shifted unary root suffices for the padded
function of [PS10, Lemma 64.3], with the original polynomial runtime bound on
the evaluator of the source function.

**Proof sketch.** Evaluate the length polynomial on the shifted root and
prepend a token to obtain the restored parameter. Split the input at the
unary length. Keep the suffix and a word of zeros while applying the source
evaluator to the encoded parameter and prefix. Concatenate the results and
cut at the length of the zero word. The sharper unary polynomial and payload
bounds charge both potentially superlinear calls against the original
input. At the empty input the final cut yields the empty word. -/
private theorem exists_linearTime_padded_of_shifted_root {F : List Bool → List Bool}
    {M : FinTM Bool} {C c : ℕ}
    (hM : M.ComputesFunInTime F (fun k => C * (k + 1) ^ c)) (ℓ : PolyExpr) {d n₁ : ℕ}
    (hd : 1 ≤ d) (hdom : ∀ n ≥ n₁, ℓ.eval n + C * (2 * n + 3 + ℓ.eval n) ^ c ≤ n ^ d)
    (hroot : ∃ (R : FinTM Bool) (a : ℕ), R.ComputesFunInTime
      (fun z => List.replicate (PadQuad.nu d z.length - 1) true) (fun m => a * (m + 1))) :
    ∃ (M' : FinTM Bool) (a : ℕ), M'.ComputesFunInTime
      (fun z =>
        ((z.drop (ℓ.eval (PadQuad.nu d z.length)) ++
          F (NUPPT.advInput (PadQuad.nu d z.length) (z.take (ℓ.eval (PadQuad.nu d z.length))))) ++
          List.replicate (2 * z.length) false).take (2 * z.length))
      (fun m => a * (m + 1)) := by
  let n (z : List Bool) := PadQuad.nu d z.length - 1 + 1
  let root (z : List Bool) := List.replicate (PadQuad.nu d z.length - 1) true
  let width (z : List Bool) := List.replicate (ℓ.eval (n z)) true
  let data (z : List Bool) := z.take (ℓ.eval (n z))
  let suffix (z : List Bool) := z.drop (ℓ.eval (n z))
  let zeros (z : List Bool) := List.replicate (2 * z.length) false
  let keep (z : List Bool) := pairEncode (zeros z) (suffix z)
  let arg (z : List Bool) := NUPPT.advInput (n z) (data z)
  obtain ⟨B, hB⟩ := shifted_image_bound ℓ hd hdom
  have hB' (z : List Bool) :
      ℓ.eval (n z) + C * ((arg z).length + 1) ^ c ≤ B * (z.length + 1) := hB z
  have hr : Linear root := hroot
  obtain ⟨P, p, hP⟩ := exists_unaryPoly_succ_computesFunInTime ℓ
  have hw : Linear width := by
    refine hr.onImage P (p * (B + 1)) fun z => ?_
    have h := (computesFunInTime_iff _ _ _).1 hP (root z)
    simp only [root, List.length_replicate] at h
    change P.ComputesInTime (root z) (width z) _
    refine h.mono ?_
    rw [Nat.mul_assoc, Nat.add_mul, Nat.one_mul]
    apply Nat.mul_le_mul_left
    have hcost := hB' z
    have hrootBound := PadQuad.nu_le d z.length
    change ℓ.eval (n z) + (PadQuad.nu d z.length - 1) + 1 ≤ _
    omega
  have hparam : Linear (fun z => List.replicate (n z) true) := by
    apply (linear_prepend_true.comp hr).congr
    intro z
    rw [show n z = (PadQuad.nu d z.length - 1) + 1 from rfl, List.replicate_succ]
  have hsplit : Linear (fun z => pairEncode (data z) (suffix z)) := by
    apply (linear_split.comp (hw.pair linear_id)).congr
    intro z
    rw [pairSplitAt_pairEncode, show (width z).length = ℓ.eval (n z) from List.length_replicate]
  have hprefix : Linear data :=
    (linear_fst.comp hsplit).congr fun z => pairFstD_pairEncode _ _
  have hsuffix : Linear suffix :=
    (linear_snd.comp hsplit).congr fun z => pairSndD_pairEncode _ _
  have hkeep : Linear keep := linear_double_zeros.pair hsuffix
  have harg : Linear arg := (hparam.pair hprefix).congr fun z => (NUPPT.advInput_eq _ _).symm
  let stage (z : List Bool) := pairEncode (keep z) (arg z)
  let result (z : List Bool) := pairEncode (keep z) (F (arg z))
  obtain ⟨V, a, hV⟩ := hkeep.pair harg
  obtain ⟨Q, hQ⟩ := exists_pairMapSnd_computesInTime M
  have hresult : Linear result := by
    refine Linear.onImage (f := stage) ⟨V, a, hV⟩ Q (40 * (B + a + 1)) fun z => ?_
    have hF := (computesFunInTime_iff _ _ _).1 hM (arg z)
    refine (hQ (keep z) (arg z) _ _ hF).mono ?_
    rw [Nat.mul_assoc, Nat.add_mul, Nat.add_mul, Nat.one_mul]
    apply Nat.mul_le_mul_left
    have hlen : (stage z).length ≤ a * (z.length + 1) :=
      length_le_time ((computesFunInTime_iff _ _ _).1 hV z)
    have hcost := hB' z
    change C * ((arg z).length + 1) ^ c + (stage z).length + 1 ≤ _
    omega
  have hzero := (linear_fst.comp linear_fst).comp hresult
  have htail := (linear_snd.comp linear_fst).comp hresult
  have hvalue := linear_snd.comp hresult
  have hjoined := (htail.append hvalue).append hzero
  have hfinal := linear_fst.comp (linear_split.comp (hzero.pair hjoined))
  apply hfinal.congr
  intro z
  simp only [result, keep, pairFstD_pairEncode, pairSndD_pairEncode, pairSplitAt_pairEncode,
    zeros, List.length_replicate]
  cases z with
  | nil => simp only [List.length_nil, Nat.mul_zero, List.take_zero]
  | cons b z =>
      simp only [data, suffix, arg, n,
        restored_root hd (by simp : 1 ≤ (b :: z).length)]


/-- In degree one the shifted root is the input length minus one. Emit one
true token for every bit following the first input bit. -/
private theorem linear_shifted_root_one :
    Linear (fun z => List.replicate (PadQuad.nu 1 z.length - 1) true) := by
  let δ := fun (_ : Bool) (_ : Bool) => true
  let emit := fun (seen : Bool) (_ : Bool) => if seen then some true else none
  have h : Linear (transduce δ emit false) :=
    ⟨transducerTM δ emit false, 1, by
      simpa only [Nat.one_mul] using transducerTM_computes δ emit false⟩
  have htrue (z : List Bool) : transduce δ emit true z = List.replicate z.length true := by
    induction z with
    | nil => rw [transduce_nil]; rfl
    | cons b z ih => rw [transduce_cons, show δ true b = true from rfl, ih]; rfl
  have hnu (m : ℕ) : PadQuad.nu 1 m = m :=
    le_antisymm (PadQuad.nu_le _ _) (PadQuad.le_nu le_rfl (by simp only [pow_one, le_refl]))
  apply h.congr
  intro z
  rw [hnu]
  cases z with
  | nil => rw [transduce_nil]; rfl
  | cons b z => rw [transduce_cons, show δ false b = true from rfl, htrue]; rfl

/-- In degree at least two the shifted root is small enough for a
quadratic budget in its numerical value. -/
private theorem shifted_root_sq_le {d : ℕ} (hd : 2 ≤ d) (m : ℕ) :
    (PadQuad.nu d m - 1 + 1) ^ 2 ≤ m + 1 := by
  by_cases hm : 1 ≤ m
  · rw [restored_root (by omega : 1 ≤ d) hm]
    have hpos : 0 < PadQuad.nu d m :=
      PadQuad.le_nu (by omega : 1 ≤ d) (n := 1) (by simpa only [one_pow] using hm)
    exact (Nat.pow_le_pow_right hpos hd).trans
      ((PadQuad.nu_pow_le (by omega : 1 ≤ d) m).trans (Nat.le_succ _))
  · have hm0 : m = 0 := by omega
    have hnu : PadQuad.nu d m = 0 := Nat.eq_zero_of_le_zero ((PadQuad.nu_le _ _).trans hm0.le)
    rw [hnu, hm0] <;> decide

/-- A multitape machine computes the shifted unary floor root in linear time.

**Proof sketch.** Degree one uses the single scan. For higher degrees,
compute the input length in binary and use the binary search on that word.
Its polynomial in the binary width is linear in the original length.
Convert the resulting canonical binary root to unary with the emitting
loop. On a canonical word the iteration count is linear in the represented
value and the polynomial in its width is also linear in that value.
The square of the shifted root, after restoring one, is bounded by the
original length plus one. -/
private theorem exists_linearTime_shifted_root (d : ℕ) (hd : 1 ≤ d) :
    ∃ (M : FinTM Bool) (a : ℕ),
      M.ComputesFunInTime (fun z => List.replicate (PadQuad.nu d z.length - 1) true)
        (fun m => a * (m + 1)) := by
  rcases eq_or_lt_of_le hd with he | hh
  · subst d
    exact linear_shifted_root_one
  · let v (z : List Bool) := PadQuad.nu d z.length - 1
    let enc (z : List Bool) := Nat.bits (v z)
    obtain ⟨L, a, hL⟩ := computesFunInTime_lengthBits
    obtain ⟨B, C, c, hB⟩ := (polyTimeComputable_iff _).1
      (polyTimeComputable_shifted_root d hd)
    obtain ⟨A, hA⟩ := exists_pow_width_bound c
    have henc : Linear enc := by
      refine Linear.onImage ⟨L, a, hL⟩ B (C * A) fun z => ?_
      have h := (computesFunInTime_iff _ _ _).1 hB (Nat.bits z.length)
      rw [bitsVal_bits] at h
      refine h.mono ?_
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left C (hA z.length)
    obtain ⟨U, K, k, hU⟩ := exists_binaryToUnary
    obtain ⟨H, hH⟩ := exists_pow_width_bound k
    refine henc.onImage U (K * H * 4) fun z => ?_
    have h := (computesFunInTime_iff _ _ _).1 hU (Nat.bits (v z))
    rw [bitsVal_bits] at h
    refine h.mono ?_
    have hcost := Nat.mul_le_mul_left K (hH (v z))
    have hwidth := two_pow_width_le (v z)
    have hR : 2 ^ (Nat.bits (v z)).length + 2 ≤ 4 * (v z + 1) := by omega
    calc K * ((Nat.bits (v z)).length + 1) ^ k * (2 ^ (Nat.bits (v z)).length + 2)
        ≤ K * (H * (v z + 1)) * (4 * (v z + 1)) := Nat.mul_le_mul hcost hR
      _ = K * H * 4 * (v z + 1) ^ 2 := by ring
      _ ≤ K * H * 4 * (z.length + 1) :=
        Nat.mul_le_mul_left _ (shifted_root_sq_le (by omega) z.length)

/-- The word formula of the Levin padded family has a linear-time evaluator.

**Proof sketch.** Combine the unary root construction with the padding
assembly, charging polynomial evaluation and the source call against the
original input length. [PS10, Lemma 64.3] -/
theorem exists_linearTime_padded {F : List Bool → List Bool} {M : FinTM Bool} {C c : ℕ}
    (hM : M.ComputesFunInTime F (fun k => C * (k + 1) ^ c)) (ℓ : PolyExpr) {d n₁ : ℕ}
    (hd : 1 ≤ d) (hdom : ∀ n ≥ n₁, ℓ.eval n + C * (2 * n + 3 + ℓ.eval n) ^ c ≤ n ^ d) :
    ∃ (M' : FinTM Bool) (a : ℕ), M'.ComputesFunInTime
      (fun z =>
        ((z.drop (ℓ.eval (PadQuad.nu d z.length)) ++
          F (NUPPT.advInput (PadQuad.nu d z.length) (z.take (ℓ.eval (PadQuad.nu d z.length))))) ++
          List.replicate (2 * z.length) false).take (2 * z.length))
      (fun m => a * (m + 1)) :=
  exists_linearTime_padded_of_shifted_root hM ℓ hd hdom (exists_linearTime_shifted_root d hd)


end TCSlib.Cryptography.PadQuad

## ===== TCSlib/Cryptography/Asymptotic/UniversalPadding/Parameter.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.Order.Ring.Nat

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The parameter recovered by Levin padding

The padded family recovers a parameter from every input length by taking the largest natural number whose fixed power fits within that length. The public equations and bounds are the interface for the machine proof.

## Main definitions

* `TCSlib.Cryptography.PadQuad.nu` is the recovered parameter.

## Main results

* `nu_pow_le`, `nu_le`, `lt_succ_nu_pow` and `le_nu` characterize its bounds.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010. (§2.13, Lemma 64.3.)
-/

namespace TCSlib.Cryptography.PadQuad

/-- The parameter recovered from the input length `m`: the largest `n ≤ m` with `n^d ≤ m`
(`ν m = ⌊m^{1/d}⌋`). -/
def nu (d m : ℕ) : ℕ := Nat.findGreatest (fun n => n ^ d ≤ m) m

/-- The recovered parameter is the greatest bounded natural number whose
degree-d power fits within the input length. -/
theorem nu_eq (d m : ℕ) : nu d m = Nat.findGreatest (fun n => n ^ d ≤ m) m := rfl

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

end TCSlib.Cryptography.PadQuad
