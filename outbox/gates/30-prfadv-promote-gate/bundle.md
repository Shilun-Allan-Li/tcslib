## ===== briefs/pass-shelat-ch5-8/gates/30-prfadv-promote/pack.md =====

# Gate 30 · Promotion of `prfAdv_eq_expect` to the PRF layer (DL-44 F-01)

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews). A small
promotion/refactor PR: one new public lemma and one proof-only re-derivation.

- **PR:** draft [PR #314](https://github.com/Shilun-Allan-Li/tcslib/pull/314) at
  `5757bc0604527602d790a1a57e9703374ce02c7b` (branch `promote/pass-shelat-prfadv-expect`, tree
  `6e784db3a2644929e03e47727c075eaf1e5908d1`).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4` on base
  `8aefdab4cdb372d0787a9be83bc65f1567ceb8b4` (the merge base; the tip after the #311 merge).
  - From the base to the records tip `f52a24be7442013d00bef3608ce5336429dd4719` there are 10 commits. Their only
    non-record paths are #312's `Complexity/Randomized.lean` and `Complexity/Randomized/SeedMajority.lean` and
    `machine-library-design.md`. Re-checked for this pack from git objects: no path is shared with the PR; neither
    module is in the head closure of a changed file (164 files); the only tip modules downstream of both are root
    `TCSlib` and `audits/pass-shelat/Checks` (import aggregators). `git merge-tree --write-tree` of the tip with the
    head gives tree `288b72c6aae4d80812b1ec21365a7fb72d696e10` with no conflict.
  - `pr.diff.txt` is `git diff origin/cryptography/pass-shelat-ch2-4...5757bc06`, which equals `8aefdab4..5757bc06`
    byte for byte.
- **Commits:** 1, by the maintainer (author and committer Claude): `5757bc06` "Promote prfAdv_eq_expect to the PRF
  layer (DL-44 F-01, Seyoon 2026-11-15)". It was first cut as `384229b08d2f6d6500e92d3f40222551abd5ecbb` on
  `99a38e3a` and rebased once onto `8aefdab4` after #311 merged; `git range-diff` gives `=` (identical patch;
  `evidence/checks/rebase-range-diff.txt`).
- **Scope:** a **promotion audit**. Seyoon's ruling on prf-mac finding F-01 (2026-11-15, "promote it now"): publish the
  generic PRF-advantage identity beside `prfAdv`, and re-derive the encrypt-then-tag copy from it with a proof-only
  change that keeps its API. prf-mac then re-points its local `hadv` by a proof-only landing edit on its own landing
  branch; that edit is **not** part of this PR.

## What changed

Paths are under `TCSlib/Cryptography/`. 2 Lean files, both modified (40 insertions, 8 deletions).

| File | Lines | Change |
|---|---:|---|
| `Pseudorandom/Functions/Defs.lean` | 106 → 142 | one import; one `## Main results` bullet; `section Expect` (`open Games ProbComp`) after `prfAdv_nonneg` with the new theorem |
| `Encryption/PrivateKey/EncryptThenTag/Reduction.lean` | 395 → 391 | `ETTGame.prfAdv_eq_expect`: body replaced by the new lemma; one docstring sentence inserted |

The new theorem (namespace `TCSlib.Cryptography`, the namespace of `prfAdv`; `I O : Type` from the file's
`variable`; formula docstring, proof sketch, no attribute):

```lean
theorem prfAdv_eq_expect {K ρ : Type} [Fintype K] [Nonempty K] [Fintype I] [DecidableEq I]
    [Fintype O] [Nonempty O] [Fintype ρ] [Nonempty ρ] (F : K → I → O)
    (A : OracleAdversary ρ I O) :
    prfAdv F A =
      |expect (sample K)
          (fun k => expect (sample ρ) fun c => if (A c).eval (F k) = true then (1 : ℝ) else 0) -
        expect (sample (I → O))
          (fun R => expect (sample ρ) fun c => if (A c).eval R = true then (1 : ℝ) else 0)|
```

Its proof is the ETT proof verbatim (`rw [prfAdv_def, distAdv_def, Bridge.acceptProb_eq ×2, accept_eq ×2,
Bridge.acceptGame_eq ×2, prob_bind ×2]`, then `prob_bind`, `prob_pure`, `oracleDist_apply`, `randomFunction_apply`).
It generalizes `ETTGame.prfAdv_eq_expect` from `K = I = O = {0,1}^m` to any finite nonempty key, input, output and
coin types (in `Type`). `ETTGame.prfAdv_eq_expect` is now `:= TCSlib.Cryptography.prfAdv_eq_expect Fm A'`.

**Statements:** decls2 against `8aefdab4` gives 1 ADDED (the new theorem), 0 CHANGED, 0 REMOVED
(`evidence/statements/decls2-vs-8aefdab4.tsv`, `.err` empty). All 20 pre-existing declaration headers of the two files
are byte-identical (`evidence/statements/header-bytes-vs-8aefdab4.txt`; the one MISSING row is the new theorem).
`touched`: 1 ADDED, 1 CHANGED (`ETTGame.prfAdv_eq_expect`, body and docstring), 20 UNCHANGED. Re-checked for this pack
from git objects with `maintainer/tools/decls2.py`'s parser: 1 ADDED, 20 unchanged.

## Rulings and records in force

1. **F-01 (Seyoon, 2026-11-15): promote it now.** The prf-mac delivery's local `hadv` in `Bound.exists_forgeGame_le`
   re-proved the public `ETTGame.prfAdv_eq_expect` (from #306) line for line (`records/…/fills/prf-mac/final-r1/review.md`,
   F-01, major). The ruling: a small PR publishes `prfAdv_eq_expect` in the PRF layer beside `prfAdv`
   (`Pseudorandom/Functions/Defs.lean` is not prf-long-owned), re-derives the ETT copy proof-only, and then prf-mac
   re-points. Decision-log rows of 2026-11-15 (the prf-mac review row with the ruling, and the promotion row).
2. **DL-44 (duplication ledger, open).** F-01 is paid by this PR (and prf-mac's re-point). F-02, F-03 and **the private
   `prfAdv_prfReduction` in `Encryption/PrivateKey/OracleFromPRF.lean`** (the same identity specialised to the
   CPA reduction, DL-40) stay in the deferred cleanup. **Not a finding:** that private copy remaining. What you can
   raise: another copy of the identity, public or private, that this PR should re-point or that the ledger misses.
3. **The PRF layer is read-only for `prf-long`.** The running `prf-long` job (final delivered 2026-11-15, under review)
   lists `Pseudorandom/Functions/Defs.lean` as read-only and owns `Asymptotic/Defs.lean`, the facade
   `Pseudorandom/Functions.lean` and `FromPRF*` (`records/…/fills/prf-long/issued-r1/brief.md`). This PR touches none
   of the owned files; no new module was created, so the facade is not edited.
4. **Rule 10.** `PolyExpr.eval` is notation (Q1, 2026-11-07; seal A canonical, B also reported); a `CoeFun`/`Coe`
   instance whose body is a structure projection is notation (Seyoon, 2026-11-14; coe seals canonical, strict run and
   attributed). For this PR strict and coe agree in every row.
5. **Lint, #305 baseline.** `campaign_style_lint.py TCSlib/Cryptography --check8b` gives **92 FAIL / 101 WARN** at
   the parent and at the head, with identical FAIL and WARN lines; the full diff is the two INFO lines (line counts,
   and Defs' public count 7 → 8) (`evidence/lint/`).

## Questions for the audit

**1. Placement**
- Is `Pseudorandom/Functions/Defs.lean`, beside `prfAdv`/`prfAdv_def`/`prfAdv_nonneg`, the right home, and is the name
  `TCSlib.Cryptography.prfAdv_eq_expect` (no `PRF` namespace exists in this layer) appropriate? Is `section Expect`
  with `open Games ProbComp` scoped so that it changes nothing for the rest of the file?
- Is the statement as general as it should be (finite nonempty `K`, `I → O` and `ρ`; `K ρ : Type` where the file's
  `variable` has `Type*`, because the game layer's `sample` is in `Type`), and are the `Nonempty` hypotheses needed?
- Are the formula docstring, its source tag `[Gar26, Definition 3.9]` (the tag `prfAdv` itself carries) and the
  proof sketch accurate, and is the new Main-results bullet right?

**2. The new import (acyclic and justified)**
- `Defs.lean` now imports `TCSlib.Cryptography.Games.Bridges.Experiments` (for `Bridge.acceptProb_eq`,
  `Bridge.acceptGame_eq`, `accept_eq`, `expect`, `sample`, `prob_bind`, `prob_pure`). `evidence/checks/imports.txt`:
  the closure of `Experiments` (7 modules) does not contain `Defs`, so there is no cycle; the import adds
  `Games.Probability`, `Games.Advantage` and `Games.Bridges.Experiments` to the closures of `Defs` (6 → 9) and the
  facade `Pseudorandom.Functions`; 42 of the 95 modules downstream of `Defs` gain them; 0 to `EncryptThenTag/Reduction`
  (163) and to root `TCSlib`. `Defs` already depended on the game layer through `OracleAdversary` → `Games.OracleComp`.
  Is the import acyclic, justified, and free of layering or name-resolution effects on the 42 modules that gain it?
- Every rebuilt module with a same-source reference built a byte-identical olean (127 of 129; the two #311 modules
  have no reference; `landing/build-refcmp.txt`). Does that settle that no downstream elaboration changed?

**3. The ETT re-derivation (proof only, API unchanged)**
- Is `ETTGame.prfAdv_eq_expect`'s header byte-identical (`evidence/statements/docstring-header-ETT.txt`) and is the
  only other change one inserted docstring sentence (`evidence/statements/docstring-delta-ETT.txt`)? Do its uses in
  `EncryptThenTag.lean` (`ccaScheme_cca2`, lines 730 and 732) and in `exists_tagStep` build unchanged
  (`landing/root-checks.jsonl`)?
- The ETT docstring's first paragraph still reads "(PRFGame overlap: `prfAdv_prfReduction`, re-derived here in general
  form from the published readers)", now followed by "This is the published `TCSlib.Cryptography.prfAdv_eq_expect` at
  `K = I = O = {0,1}^m`.", and its sketch still lists the rewrite chain. The maintainer's open point: is the first
  paragraph now stale (a minor), or still accurate as a record of the PRFGame overlap?

**4. Other copies of the identity**
- Known and deferred: the private `prfAdv_prfReduction` (`OracleFromPRF.lean:286`, same rewrite chain specialised; DL-44,
  DL-40). Known and to be re-pointed after this merges: prf-mac's local `hadv` (on the unmerged landing branch
  `land/pass-shelat-prf-mac` at `bd45faec`, not on the tip).
- Checked by the maintainer for this pack, at the head (`git grep` for `prfAdv_def` and `Bridge.acceptProb_eq`): the
  other uses are `FromPRF/Hybrid.lean:162` and `GGM.lean:254` (hybrid chains rewriting `prfAdv_def, distAdv_def` into
  hybrid probabilities, not this identity), `Asymptotic/Defs.lean:435` (`prfAdv_toOracleAdversary`, a `rfl` reading),
  and `PublicKey/BitwiseCPA.lean:392`, `OracleSecurity/PaddedCPA.lean:264` (one acceptance probability as an
  expectation over a product sample, no `prfAdv`). Are there copies this list misses, and should any be re-pointed
  here rather than in the cleanup?

**5. Rule 10**
- Seals A and B, strict and coe, pass for both changed files (requests: `Defs` strict 72/72, coe 71/71; `Reduction`
  strict 2271/2272, coe 2270/2271; `evidence/rule10/seals-*.tsv`). The paired controls (rows `prfAdv` with reader
  `prfAdv_def`, `ProbComp.expect` with `expect_pure`, `uprob`, and `PolyExpr.eval` in B) are ALL_OK in both harnesses
  (8 probes and 11 sealed negatives each; `evidence/rule10/ctlcheck-*.log`); `prfAdv` is `Defs`' own definition, so it
  is not in `Defs`' request set. Does the new proof read only published readers (`prfAdv_def` is the defining file's
  reader of `prfAdv`)? No explicit-unfold scan was run for this PR; the new proof's `rw`/`simp only` lists name only
  the theorems quoted above.

## Known dispositions (not findings)

- **The interaction with #313** (Gate 29, `learning`). `Defs.lean` is in the learning unit's closure (through
  `FromPRF/HybridLemmas` and the PRF layer), so this PR adds the three game-layer modules to it. `git merge-tree
  --write-tree 8befc589 5757bc06` gives tree `647c2e96fbb887ce32cd094d08536f7d1a57a8e8` with no conflict. The combined
  tree has not been built; whichever PR merges second is rebuilt on the merged tip.
- **The interaction with prf-long and prf-mac.** prf-long's owned modules are downstream of `Defs`; its landing rebuilds
  on whatever tip it lands on. `MAC/FromPRF` (prf-mac's owned module, still admitted on the tip) is among the 42 modules
  that gain the import; prf-mac's landing is rebuilt with its re-point.
- **The base advance after the cut** (`evidence/checks/base-advance-8aefdab4-to-711a9f4a.txt`): #312 is in neither
  changed file's closure, `Defs` is not in #312's closure, and the only shared downstream modules are root `TCSlib`
  and `audits/pass-shelat/Checks`, so the branch was not rebased a second time.
- **The build ran on a tree at the `eff2dcd0` base**, so its 129-module queue is the 96 modules downstream of the two
  files united with the 63 of the #303–#309 and #311 base delta and its downstream. The 10 sorries are all
  pre-existing (MAC/FromPRF 1, SpecialEncryptionSecurity 3, #311's SpecialEncryptionMulti 1, GarblingSecurity 1, Yao
  3, Randomness/Learning 1).
- **The PR description differs from the records draft.** `records/…/promote-prfadv-2026-11-15/pr-body.md` (also in the
  evidence ZIP; its `PROVENANCE.txt` calls it "draft PR description (not opened; nothing pushed)") is the long draft.
  The opened PR's description (`pr-description.md`, fetched 2026-11-15) is a shorter rewrite; its displayed signature
  omits the binders and instance arguments and writes `if (A c).eval (F k) then 1 else 0`. The Lean file is
  authoritative. What you can raise: a claim in either description that is false.

## Also check

**Axioms:** `TCSlib.Cryptography.prfAdv_eq_expect`, `ETTGame.prfAdv_eq_expect`, `ETTGame.exists_tagStep` and
`Composability.ccaScheme_cca2` each print `[propext, Classical.choice, Quot.sound]`; the log also has the `#check` of
the elaborated statement (`landing/axioms-head.txt`).

**Sizes and widths:** `Defs.lean` 142 lines (max width 97), `Reduction.lean` 391 (max 99) (`source-head.json`,
`evidence/checks/widths.txt`).

**Build:** 129/129 rc 0, 0 errors in both diagnostic forms, through root `TCSlib`, `audits/garg-ch1-3/Checks` and
`audits/pass-shelat/Checks` (`landing/root-checks.jsonl`, whose last line is the runner's `done` record); the olean
tree was restored to the base snapshot (`evidence/restore/tree-check-post.txt`).

## Evidence

- **`verification.zip`** (38 entries): byte-identical originals; `SHA256SUMS` lists every other entry and
  `PROVENANCE.txt` gives each entry's source.
  - `promote-prfadv-evidence.zip` (`maintainer/promote-prfadv-2026-11-15/`, SHA-256 `3c9a9f32…`) and
    `evidence-SHA256SUMS`, its manifest: 732 entries, 66 directory entries and 666 files, exactly the 665 manifest
    paths plus `SHA256SUMS` (byte-identical to the manifest); every hash verifies. It covers the patch and diff, the
    rebase, imports, statements, the build with the olean comparison, axioms, seals and controls, lint, the restore,
    and the pre-rebase run (`pre-rebase-384229b0/`);
  - `records/`: `PROVENANCE.txt` and `pr-body.md` beside the ZIP (each equal to the ZIP entry), the decision log, the
    duplication ledger, the prf-mac review and the issued prf-long brief, at records
    `f52a24be7442013d00bef3608ce5336429dd4719`;
  - `evidence/`: byte copies of the ZIP entries this pack cites.
- **`landing/`:** byte copies of evidence-ZIP entries: `root-checks.jsonl` (= `build/results.jsonl`),
  `build-refcmp.txt` (= `build/refcmp.txt`), `axioms-head.txt` (= `axioms/AxiomsHead.log`).
- **`pr-description.md`:** the PR #314 description as fetched from the GitHub REST API on 2026-11-15 (`.body`, raw).
- **`pr.diff.txt`:** `git diff` from the base to the head (2 paths, 40 insertions, 8 deletions).
- **`source-head.json`:** the head hashes, line counts and over-width counts of the 2 changed files.
- **`sources.zip`:** the source closure at the head of both changed modules, 164 files.

## Findings delivery

Return `gate30-prfadv-promote-findings.md` as a Markdown file in this chat. If you have several evidence files, return
a ZIP. The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable statement, a changed API of `ETTGame.prfAdv_eq_expect`, a cycle, or a scope
  violation (a prf-long-owned file touched).
- **major:** a changed frozen statement, a forbidden read not covered by the rulings, an undisclosed copy left behind
  that this PR claims to remove, or necessary evidence that cannot be verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring or proof sketch.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.

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

## ===== briefs/pass-shelat-ch5-8/fills/prf-mac/final-r1/review.md =====

# prf-mac · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS.** One finding, F-01, is resolved by Seyoon's ruling: the duplicated lemma is
promoted first, in a separate PR, and prf-mac then re-points to it. The landing branch waits for that PR.

## Delivery and landing branch

**The delivery**
- **Worker and target.** A Claude worker proved `Authentication.prfMAC_secure`, [PS10, Theorem 135.4].
- **Exchange.** The final is at `51ae2c1215554ccda3dde19d8d72908ea74dd339`. Checkpoints were delivered at `f93d8a02` and `22b70519`.
- **Base.** The issue base is `107f1e8c`.

**The landing branch** `land/pass-shelat-prf-mac`
- **Head:** `bd45faecffa420497557dfeba9e2818d7d3cf4a3`, tree `25ad7a637d6c33353df4e463e02e2816e07d2aa2`.
- **Rebase:** it is rebased onto records tip `e7fa2605`. That tip includes #303 and #306–#309. The rebase had no conflict, and the Lean content is unchanged.
- **The worker's 4 commits:** `d8fb2380`, `99929a43`, `0872e5c1` and `fa72acc6` (Rule 10 repair).
- **LE-doc** `bd45faec`: two docstring-only formula fixes, one on `PRFMAC.macHandler`'s `simps` fields and one on the `FnForge` Decidable instance. The code is identical with doc comments blanked.

**Files**
- The owned file `MAC/FromPRF.lean` changes.
- Five helpers are new: `MAC/FromPRF/{Bound,Game,Handler,Random,Reduction}.lean`.
- No other file changes.

**Evidence:** `review-evidence.zip`, SHA-256 `e8038014cc178de78f93f194434f20795b396e1c918fa7d1140e5dd74e49cad5`.
- It has 373 entries, the manifest plus `SHA256SUMS`, and its manifest is `evidence-SHA256SUMS`.
- The overlap searches are in `landing/overlap-review.txt`.

## Checks
- **Integrity**
  - The manifests verify 693/693 and 680/680, with exact paths.
  - The issue package verifies 7/7, and its sources 208/208.
  - `git am` reproduces the 4 worker hashes. This works only with the environment's deterministic SSH commit signature (F-05).
- **Build**
  - 67 modules give rc 0 and 0 errors (both diagnostic forms). They are the 57 changed modules (51 base delta plus the unit's 6) and their downstream, through root `TCSlib` and `audits/pass-shelat/Checks`.
  - The whole-tree check at the head covers 1246 modules: OK.
  - There are no name clashes with #307, #308 or #309.
- **Statements:** decls2 gives 38 ADDED, 0 CHANGED, 0 REMOVED. All headers are byte-identical, the target's included.
- **Axioms:** the target uses only the standard three axioms. So do all 97 stored constants. There is no `@[simp]` and one instance.
- **Rule 10**
  - Seals A and B pass in both the strict and the coe variant: 6/6 at the head, 1/1 at the base.
  - Paired controls: 16 probes, 68 negatives, ALL_OK.
  - The explicit-unfold scan finds 0 foreign definitions.
- **Admissions:** 20 → 18. The two removed are `prfMAC_secure` and `dlHash_crh` (from #307).
- **Lint:** 92/101 at the tip and at the head, with identical lines. Widths are at most 100 characters.
- **Content**
  - The proof gives `Pr[forge] ≤ prfAdv(F_n, D^{q·1+1}) + 2⁻ⁿ` at every `n`.
  - It handles the edge cases: `n = 0`, budget 0, repeated queries, a queried output message, timeouts, and the `+1` final query.
- **Tooling:** the review runner was fixed to count both `error:` and `error(` (G26-N1).

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| F-01 | major | **Undisclosed duplicate.** The local `hadv` in `Bound.exists_forgeGame_le` re-proves the public `ETTGame.prfAdv_eq_expect` (from #306) line for line. | **Ruling (Seyoon, 2026-11-15): promote it now.** A small PR promotes `prfAdv_eq_expect` to the PRF layer, beside `prfAdv`, and re-derives `ETTGame.prfAdv_eq_expect` from it with a proof-only change that keeps that API. prf-mac then re-points `hadv` to the promoted lemma with a proof-only landing edit. |
| F-02 | minor | **Undisclosed restatement.** `decide_fnForge`'s `hw`, `htake` and `hdrop` restate list readings of `splitBits`. The public relatives are `take_ofFn_castLE`, `CollectionsHelpers.ofFn_drop_take`, and, since #307, `FromDiscreteLog.ofFn_splitBits_fst`/`_snd`. | Erratum; ledger DL-44. |
| F-03 | minor | **Undisclosed nearest relative.** The `blocks`/`macState` encoding and `hits_nil_iff` have an undisclosed nearest relative, `GGMRed.tblEnc`/`lookup` (reused by cca2-ett as `tblW`). This is a different encoding, not a restatement. | Erratum; ledger DL-44. |
| F-04 | note | **Incomplete relative lists.** The rows for `key`/`hkey` and for `accept_forgeGame_eq` are incomplete. The missing relatives are `NUPPT.coinsEquiv_ofPolyTimeUniform(_ofFn)`, `ofFn_arrowCongr_finCongr` and Lamport's deterministic-signer lemmas. | Erratum. |
| F-05 | note | `COMMITS.tsv` hashes reproduce only with the environment's deterministic SSH commit signing. | Future briefs must record the signing or require `commit.gpgsign=false`. |
| F-06 | note | Two pre-existing items, both disclosed: the target's frozen first docstring paragraph has no formula, and the base `prfMAC.correct` has no proof sketch. | None. |

## ===== briefs/pass-shelat-ch5-8/duplication-ledger.md =====

# Duplication ledger: Pass–shelat ch. 5–8

Accepted debt, each entry acknowledged by the user, with its scheduled resolution.

| ID | New declaration (where) | Existing copy (where) | Status | Resolution |
|---|---|---|---|---|
| DL-1 | `TCSlib.InformationTheory.abs_probTrue_sub_le_statDist` (#183, `InformationTheory/Extractors.lean`, for `main`) | `TCSlib.Cryptography.abs_sum_sub_le_statDist` (`Foundations/Experiments.lean`, Garg's concrete layer, on `cryptography/pass-shelat-ch2-4` and `cryptography/garg-ch1-3`; not on `main`) | accepted 2026-11-04 (user) | No copy on `main` today. When the concrete layer lands on `main`, its lemma becomes a one-line corollary of #183's (a `Finset` test is the `Bool` test `(· ∈ T)`) or is removed. Gate 01 pack erratum E1. |

## Inherited with ch. 2–4 (found 2026-11-05; acknowledged 2026-11-05 by the user: clean up now)

This campaign owns ch. 2–4 since 2026-11-05 (plan, decision log). These duplicates predate it.

| ID | Copies (where) | Status | Proposed resolution |
|---|---|---|---|
| DL-2 | XOR of encodings is the encoding of the Boolean sum, `zipWith xor (ofFn a) (ofFn b) = ofFn (a + b)`, stated three times: `TCSlib.Cryptography.zipWith_xor_ofFn_add` (`Asymptotic/HardCoreLoops.lean`; it was `zipWith_xor_ofFn`, renamed by the base repair to end the name clash with `Encryption.lean`'s different lemma); `TCSlib.Cryptography.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessage.lean`); `TCSlib.Cryptography.MultiMsg.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessageLemmas.lean`) | accepted; scheduled now | Keep the most upstream copy (`HardCoreLoops`) and point the other two at it, in a ch. 2–4 cleanup PR. |
| DL-3 | `pairEncode a b ≠ []`, stated four times: `GGMRed.pairEncode_ne_nil` (`Asymptotic/GGMReduction.lean`), `GI.pairEncode_ne_nil` (`ZeroKnowledge/GraphIsomorphism/Proofs.lean`), `ColMachines.pairEncode_ne_nil` (`ZeroKnowledge/ThreeColoring/Machines.lean`); and, on `main`, `Complexity.pairEncode_ne_nil` (`Complexity/SpaceComplexity/Logspace/InputAccess.lean`), the copy that made the merge's ambiguity | accepted; scheduled now | `main` is merged (#186). Remove the three local copies in favour of `Complexity.pairEncode_ne_nil`, in the same cleanup PR. |
| DL-4 | Not a copy (different carriers): the sampler-based `StatClose` (`Asymptotic/Sampling.lean`) and `main`'s `EpsClose` on `FinDist` (`InformationTheory/Extractors.lean`, #183) | accepted; scheduled now | A bridge lemma, in the same cleanup PR (user, 2026-11-05). |
| DL-5 | Not a copy (different carriers; found by the gate 02 round 2 review): `Games.guessAdv_eq_half_advantage` and `Games.accept_guessGame` (games) and the concrete layer's `predict_eq` (`Asymptotic/Ensembles.lean`, on `uprob` over seed spaces), both the identity behind [PS10, Lemma 73.8] | disclosed in the docstring (gate 02 closing commit) | Derive one from the other through bridge B2 when ch. 2–4 lands on `main`. |

## Found in the ch. 5–8 statement phase (2026-11-05)

| # | Statement | Copies | Status | Resolution |
|---|---|---|---|---|
| DL-6 | Coin-tape slices `(r.drop (j * c)).take c` in global/GI-shadow graph isomorphism, Lamport and sequential ZK, alongside the former BlockEncryptor home | historical duplicates found by the Lamport worker/maintainer | **Implemented at `e9d64158461bfe24ddc88ab885bc4017899b4c16`; final source `3f6db40e1688c4a0bb922c9575dd3bd2157a650b` is checked in draft PR #232. Native and layered Rule10 reconciliation identify zero new/touched reads; all older failures remain recorded. External gates and landing pending.** | One `TCSlib.Cryptography.coinBlock`, `coinBlock_eq` and `length_coinBlock` live in `Asymptotic/Adversary.lean`. The BlockEncryptor definition moved upstream; global/shadow `coinSlice` and sequential ZK's `phaseSlice`/unused length lemma are retired. Lamport already used the public BlockEncryptor `coinBlock`; its length lemma moved upstream. Consumers use the shared name and published reader. |
| DL-7 | Equal-length padding: Lamport's `ofFn_padFin_of_length`, and the inline step in `Composability.length_eval_of_length` (`CCA2Scheme.lean`) | General equation `Collection.ofFn_padFin_of_le` in **`Asymptotic/CollectionsHelpers.lean`**, not `Collections.lean` | **Implemented at `e9d64158461bfe24ddc88ab885bc4017899b4c16`; final source `3f6db40e1688c4a0bb922c9575dd3bd2157a650b` is checked in draft PR #232. Native and layered Rule10 reconciliation identify zero new/touched reads; all older failures remain recorded. External gates and landing pending.** | Lamport's duplicate theorem is deleted. Its uses and CCA2's two padding steps use the general equation, whose conclusion is `List.ofFn (padFin ℓ w) = w ++ List.replicate (ℓ - w.length) false`; at `w.length = ℓ`, simplify `Nat.sub_self`, `List.replicate_zero` and `List.append_nil`. |
| DL-8 | `SecureComputation.PRFOut ℓ₂` (prong B, `SpecialEncryptionSecurity.lean`): ch. 2–4's `PRF` with `ℓ₂(n)`-bit outputs; `PRF` is its case `ℓ₂ = n` | resolved 2026-11-05 | `prfOut_var_iff : PRFOut .var F ↔ PRF F` proved beside `PRFOut` (prong B). The ch. 2–4 layer is unchanged. |


## Found by gate 03 (2026-11-05; rulings G3-5 and R-03l-1: clean up in the gate 03 clean-up PR, after #195)

Most copies trace to helpers that are `private` in pack 03a's and 03l's files. The clean-up makes
one copy public in the most upstream file and re-points the rest.

| Id | Copies | Status | Payback |
|---|---|---|---|
| DL-9 | The coin-block bijection `blocks` (`Fin (m · c) → Bool ≃ Fin m → Fin c → Bool`) and its lemmas, copies and an inverse: `FunFamily.blocks`, `OneWayYao.blocksE`, `blocksEquiv`, `blocksEquivX`, `EnsembleLemmas.blocks`, `SoundnessRep.blocksEquiv`, and `Ensemble.blocks` (private, `Asymptotic/Ensembles.lean`, which calls itself a copy of `FunFamily.blocks`; added on gate 03a round 2, R2-4); with S2b's public duplicate `take_drop_ofFn_blocks` of `EnsembleLemmas.take_drop_ofFn_blocks` (gate 04 N4) | accepted; scheduled (G3-5) | One `FunFamily.blocks` in a low file; re-point 03h, 03i, 03k's statements, `Ensembles.lean` (03a) and S2b's copy. |
| DL-10 | `ptc_comp` (composition of polynomial-time functions in a convenient form), six private or public copies (`Closure`/`Repetition` helpers, `Universal*`, `ThreeColoring/Machines`, …) | accepted; scheduled (G3-5) | Public once in 03a's `Closure.lean`; delete the copies. |
| DL-11 | The state loop `stateFind` (private in `Repetition.lean`) and its copies `GI.stateFind`, `EncodingMachines.polyTimeComputable_stateFind`, `GGMRed.stateLoopFun`, and the variant `stateIterate` | accepted; **half done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (`polyTimeComputable_stateFind` public, prose fixed); the copies are re-pointed in clean-up part 2 | `polyTimeComputable_stateFind` public in `Repetition.lean`; re-point; update the prose that calls it private (`StringLoops.lean:36–38`, `HardCoreLoops.lean:68`). |
| DL-12 | `abs_uexp_sub_le`, two copies (`PublicKeyLemmas` and a private one) | accepted; scheduled (G3-5) | One public copy. |
| DL-13 | `negligible_zero` (`Foundations/Negligible.lean` since G3-7a) and `negligible_const_zero` (`ZeroKnowledge/Defs.lean`) | accepted; scheduled (G3-5) | Delete `negligible_const_zero` (2 uses). |
| DL-14 | `forall_of_uprob_eq_one`, two copies | accepted; scheduled (G3-5) | One public copy. |
| DL-15 | `decodeFin_eq_some_iff`, a private copy in `Collections.lean` and a public one in `GGMReductionEval.lean` (`GGMRed.decodeFin_eq_some_iff`; making the `Collections.lean` copy public must avoid the namespace clash, gate 03b review #12c), and the new forward lemma `ofFn_of_decodeFin_eq_some` (`CollectionsHelpers.lean`, #198); S2b's private `eq_ofFn_of_decodeFin` | accepted; scheduled (G3-5) | One public `decodeFin_eq_some_iff` in `Asymptotic/Adversary.lean`; the forward lemma derived from it. |
| DL-16 | `IterateFindHost` (03l) copies 26 declarations of `main`'s private module layer in `Complexity/ClassNP/SAT.lean` (ten now public); the new host is missing from the policy's host registry (§14) | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)**: one public host `Turing.ModuleHost` (`TuringMachine/Build/ModuleHost.lean`), consumed by `SAT.lean` and `IterateFindHost.lean`; registry row H14 | Make `SAT.lean`'s layer public on the ch. 2–4 branch and re-point `IterateFindHost`; register the host. |
| DL-17 | `StateLoop` (03l) restates five `main` lemmas, plus `tail_poly` and `xor_poly` (arrived with the `main` merge, #186) | accepted; scheduled (R-03l-1) | Use `main`'s lemmas. |
| DL-18 | `UnaryMul` (03l) privately copies `PairSplit`'s parser | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (`Turing.PairParse` in `PairSplit.lean`) | Use `PairSplit`'s. |
| DL-19 | Not a copy yet: a latent name clash between `StateLoop.BlockLoop` and `main`'s `Complexity.BlockLoop` (nothing uses it) | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (renamed `StateLoop.BlockMapLoop`) | Rename or merge in the same PR. |
| DL-20 | `main`'s `TuringMachine/Build/Loop.lean` keeps a private `loop_first_halt`, the same lemma as the new public `Turing.ModuleHost.first_halt` (found by #203's worker). `Loop.lean` is upstream of the host, so it cannot consume it | noted | Move `first_halt` and `live_prefix` down into `Loop.lean` (or the machine core) at the `main` landing, and have `Loop.lean` use them. |
| DL-21 | Elementary number theory that Mathlib already has (audit `mathlib-overlap-nt.md`, 2026-11-06, Mathlib pin `029db123`): 6 DUP (`QR` = `(powMonoidHom 2).range`, `crtUnits` (keep as alias, `rfl`), `coprime_of_ne` = `(Nat.coprime_primes hp hq).2`, `powOneSubgroup` = `(powMonoidHom m).ker`, `rsaPerm` ≈ `powCoprime` (optional), `IsGenerator` ≈ `∀ x, x ∈ zpowers g`) and 9 WRAP (shorter proofs from Mathlib: `units_val_mem`, `pow_mod_totient_modEq`, `units_pow_eq_one_iff`, `two_mul_card_le_of_ne_top`, `card_units_eq_mul_card_QR`, `card_QR_prime`, `sq_pow_div_four_succ`, `fmultNat_eq_mul_prime`; and the core of the sorried `elGamal_correct`) | accepted; scheduled (user direction 2026-11-06: Mathlib first) | Replace by Mathlib's (alias where a name is load-bearing), clean-up part 2 item M; rows in fill-owned files (`Candidates/*`) after those fills land, as landing edits. The fill briefs cite the report's Mathlib names. |
| DL-22 | TCSlib's Chebyshev lower bound (`NumberTheory/Chebyshev.lean`) and Korselt-type facts are in newer Mathlib (`Chebyshev.pi_ge`, `theta_ge`, `psi_ge`; `Nat.isCarmichael_iff_korselt`; master `94f43000`, Lean v4.36.0-rc2), not at our pin | noted | Replace at the next Mathlib bump (repository-wide, `main`'s pin). At the same bump, the hypothesis `BlumDensity` (`Rabin.lean`) can be discharged in its eventual form (`n ≥ n₀`): apply `WienerIkehara.tendsto_sum_range_div` (master only) to `vonMangoldt.residueClass 3` mod 4, with the continuation `vonMangoldt.continuousOn_LFunctionResidueClassAux` (already at our pin) and Chebyshev's `ψ(x) ≪ x` (master), to get `ψ(x; 4, 3) ~ x/2`; then `θ ≥ ψ − (ψ − θ)` (`Chebyshev.psi_sub_theta_le_mul_sqrt`) and `π(x; 4, 3) ≥ θ(x; 4, 3)/log x`. This changes the Rabin statements that take `BlumDensity` (they would take nothing, or `n ≥ n₀`); a statement gate then. |
| DL-23 | fac fill (`Candidates/Factoring.lean`, delivery review 2026-11-07): private near-copies of public lemmas: `fac_chunkEquiv` = `FunFamily.blocks`; `fac_arrowCongr` = `finCastEquiv`; `fac_ofFn_halves` repeats a private `OneWay` lemma (half is `ofFn_block_eq_take_drop`); `fac_listToNat_inj` repeats a private `Sampling` lemma; plus the REPORT's three near-duplicates and small numeral facts re-proved across the fac, rsa and dl-a fills | noted | Clean-up part 2: re-point to the public lemmas; publish the two private ones beside their files and share the numeral facts. |
| DL-24 | col-b fill (delivery review 2026-11-07): `ColZK.acceptProb_seed_to_coins` = `acceptProb_bind` reversed and `ColZK.findSome?_map_option` = core `List.map_findSome?` (removed by landing edits E3–E4); a third copy of `pushesUniform_restrict` across fill units (dl-a has one); `table_index_*` vs `finProdFinEquiv`; `polyTimeComputable_next` repeats `reply_poly`'s proof (review finding 6 has the full list) | E3–E4 at landing; rest noted | Clean-up part 2: publish one `pushesUniform_restrict`, re-point the rest. |
| DL-25 | dl-b fill (`DiscreteLogHardcore.lean`, delivery review 2026-11-07): `dlb_statClose_pi` copies the public `OneWay.statClose_pi` (removed by landing edit E1); `dlb_stateIterate_poly` (from `HardCoreLoops`), `dlb_count_ofFn` (from `HardCoreGL`; relative of `List.count_ofFn`), the `listToNat` fold lemmas, `two_pow_size_le` (dl-a and 3-col have inline `2^size m ≤ 2m` bounds), `pushesUniform_castLE` copies (review D1) | E1 at landing; rest noted | Clean-up part 2: publish one copy of each beside its source; missing equations `HardcoreBit.majority_eq` (`PairwiseIndependence.lean`) and `expSampler_coins` (`DiscreteLog.lean`) at the next shared-file window. |
| DL-26 | col-a fill (delivery review 2026-11-07): `colRep_xor_poly` = `StateLoop.xor_poly`, `eq_of_xor_eq_false` = core `bne_eq_false_iff_eq`, `pushesUniform_blockRead` rebuilds `FunFamily.blocks` (removed by landing edits E2–E4); `ColRep.exec_four_mul`'s step repeats `GI.exec_repViews`'s proof (promote `exec_four_mul`, request R-3); cross-unit near-copies with col-b's `ColZK.pushesUniform_offsetTable`, `ColZK.ofFn_drop_take` | E2–E4 at landing; rest noted | Clean-up part 2: promote `exec_four_mul`, share the col-a/col-b helpers; requests R-2 (`(decGraph x).1` equation), R-5 endorsed. Base reading for #210's next round: `R3COL_witnessRelation`'s `bounded` clause destructures `R3COL` instead of using `R3COL_iff`. |
| DL-27 | rsa fill (delivery review 2026-11-07): 151 lines copied verbatim from dl-a's private helpers (`dla_findSome?_ite`, `dla_find?_range_lt`, `dla_listToNat_append`, `dla_drop_natToList_zero_append`, `dla_ss*`); `rsa_appendEquiv` = Mathlib `Fin.appendEquiv` (landing edit E1); `rsa_comp`/`ptc_congr` copies of the private `ptc_comp` family; loop lemmas descend from Primality's private `spStep`; near-copies of `findSome?_eq_bind_find?`, `find?_range_eq_map_find?_finRange`; parallels with fac (`fac_natToList_mod`, `fac_pairDec`) | E1 at landing; shared-lemma PR planned | **Landing order:** (1) dl-a lands; (2) a shared-lemma PR publishes `PolyTimeComputable.comp'`/`.congr` (`PolyTime.lean`), `IterateFind.find?_range_and_lt` (`IterateFind.lean`), nine `listToNat`/`natToList` lemmas (`Arithmetic.lean`), `rejectBlocksL_eq_find?` (`Concrete.lean`), removing dl-a's copies; (3) rsa lands with E1–E3 and E4 (cites them; checked against stubs); (4) a statement-gated `polyTimeComputable_rejectBlocksL` retires the copied loops in dl-a, rsa, rabin (and dl-c, pending its review). |
| DL-28 | dl-c fill (delivery review 2026-11-07): near-verbatim copies of the trial loop and numeral helpers shared with dl-a and rsa (and dl-b's own modular-numeral layer); `dlc_abs_uexp_sub_le` duplicates `Sampling.lean`'s private lemma and its public copy in `PublicKeyLemmas.lean` (review D1) | noted | Folds into DL-27's shared-lemma PR. The review's D2 homes: generic `polyTimeComputable_rejectBlocksL` (`Concrete.lean`), `listToNat` lemmas, width lemmas (`Arithmetic.lean`), `find?_range` (`Repetition.lean`), `PolyTimeComputable.congr` (`PolyTime.lean`), `abs_uexp_sub_le` public in `Sampling.lean`, `finCastEquiv` to `CollectionsHelpers.lean`. Reconcile with DL-27's homes when that PR is drafted. |
| DL-29 | rabin fill (delivery review 2026-11-07): `rabin_appendEquiv` = Mathlib `Fin.appendEquiv` and `rabin_pushesUniform_prod` (re-proved from `PushesUniform.prodMap`) handled by landing edits E1–E2; undisclosed copies: `rabin_statClose_one` = dl-a's `dla_statClose_one`; `rabin_listToNat_mulStr`, `rabin_prime_poly` copy rsa helpers; `rabin_rS`/`_rQ`/`_rTest` ≈ rsa's `rsa_fS`/`_fQ`/`_fTest`; the block loop is a fourth copy (with dl-a, rsa, dl-c `dlc_ss*`); `rabin_drop_zeros_append`'s step = fac's `fac_natToList_mod` | E1–E2 at landing; rest noted | Folds into DL-27/DL-28's shared-lemma PR and the `polyTimeComputable_rejectBlocksL` host PR. Base reads `rabinCollection_index`, `rabinBlumTrapdoor_index` (through `show`; re-point via `Collection.index_eq`) go to clean-up part 2's (b) list. |
| DL-30 | padded-cpa fill (delivery review 2026-11-11): generic `ProbComp` facts published in a public-key helper as `Composability.ChallengeSim.expect_sample_equiv`, `expect_sample_comm`, `expect_sample_unique`, `expect_sub` (`PublicKey/OracleSecurity/ChallengeSim.lean`); `expect_sample_prod` repeated `Bridge.expect_sample_pair`'s proof. | `ChallengeSim.lean` only | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Landing edit re-proved `expect_sample_prod` from `Bridge.expect_sample_pair`. Promote the four lemmas to `ProbComp` in `Games/Probability.lean` and re-point their uses. |
| DL-31 | `ofFn_padFin_of_length` (`List.ofFn (padFin d w) = w` when `w.length = d`): `GGMRed.ofFn_padFin_of_length` (`GGM/Run.lean`), copy in `Asymptotic/HardCoreGLColl.lean`, private copy in `ElGamal.lean`; padded-cpa's `RecordHandler.lean` uses the GGM one through a transitive import. | 3 | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Promote one public lemma beside `padFin` in `Asymptotic/Adversary.lean`; re-point all uses and delete the copies. |
| DL-32 | `List.ofFn (cast h f) = List.ofFn f` for a width equality: public `Composability.AdaptiveCPA.ofFn_cast` (`PublicKey/AdaptiveCPA/Games.lean`) and private `cca2OfFn_cast` (`PrivateKey/OracleFromPRF.lean`, #289). adaptive-cpa review also lists for promotion: `expect_sample_update` (→ `Games/Probability.lean`, with DL-30), `simulate_eq_of_abs` and the `castImpl` family (→ `Games/Simulate.lean`), `padFin_ofFn_zeroBits`, `headD_ofFn_one`, `ofFn_splitHalf_fst/_snd`; reader request `indCodec_eq_bitCodec`; new uses of `GGMRed.ofFn_padFin_of_length` join DL-31. | 2 (+ candidates) | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Promote one generic `ofFn_cast` beside `padFin`/`BitCodec`; re-point both; promote the listed generic lemmas. |
| DL-33 | bitwise-cpa fill (delivery review 2026-11-11): `BitwiseSim.expect_sample_update` vs `AdaptiveCPA.expect_sample_update` (two forms, same name); generic `BitwiseSim.expect_simulate_eager` and public near-copy `BitwiseSim.expect_simulate_indImpl_cpa` of the private lemma in `PublicKey/OracleSecurity.lean`; `chRun_toCompOn_transport_list` generalizes `ChallengeSim.chRun_toCompOn_transport`; `BitwiseSim.headD_drop` = public `CommitmentLemmas.headD_drop` (and private `headD_drop_ofFn` in `Pseudorandom/NextBit.lean`); `flatten_ofFn_singleton` = private `flatten_ofFn_one` (`Yao.lean`); `decodeFin_nil_getD` (→ `Games/BitCodec`); `padded_enc_runAt/_coins` (→ beside the padded readers); `qDin/qDout` third copy of the two-oracle length vector (`recDin/recDout`, `acDin/acDout`); private `ofFn_half`, `bitwise_runAtL` re-prove published facts; reader request `HybridMachine.hybridPre_eq`. | several | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | One consolidation PR with DL-30–DL-32: promote to `Games/Probability`, `Games/Simulate`, `ChallengeSim`, `BitCodec`, a shared list module; re-point and delete copies. |
| DL-34 | pk-cpa-cca1 fill (delivery review 2026-11-12): `OracleFromPRF/Handler.lean` copies private AdaptiveCPA handler pieces (`ofFn_padFin_eq_padL`, round-input readers `rU`…`rCnt`, `impl_of_ret`, `replicate_one`); public `ofFn_pkTapes` re-proves `AdaptiveCPA.ofFn_acTapes` (a generic `⟦blocks q ℓ ω j⟧ = (⟦ω⟧.drop (j·ℓ)).take ℓ` belongs beside `FunFamily.blocks`, input-layout readers beside `InteractiveHandler.input`); private-key `indCodec_eq_bitCodec` (DL-32 reader request); `mem_keys_of_lookup_isSome` (core `List.lookup_isSome_iff`); promotion candidates `simulate_eq_of_abs_bounded` (generalizes `AdaptiveCPA.simulate_eq_of_abs`), `expect_simulate_congr` (→ `Games/Simulate`), `abs_expect_sub_le` (→ `Games/Probability`), `prob_bad_le`, `expect_sample_mem_le` (→ `Games/Hopping`), `padFin_nil`, `padFin_replicate_false`, `ofFn_arrowCongr_finCongr` (→ beside `padFin`), `zipWith_xor_cancel_left`, `xorPerm` (shared list/vector module); owned-file private overlaps with the `cca2*` helpers. | several | **Paid** ([#298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), merge `d3f2290a`, 2026-11-13; Gate 20) | Fold into the DL-30–DL-34 consolidation PR. |
| DL-35 | Found while staging the consolidation (2026-11-12): public `blocks` in `Asymptotic/EnsemblesLemmas.lean` and private `blocks` in `Asymptotic/Ensembles.lean`, both the equivalence `(Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool)` of `FunFamily.blocks` (`Asymptotic/Adversary.lean`). | 2 | Open (ch. 2–4 inherited) | Re-point to `FunFamily.blocks` in a later ch. 2–4 cleanup; out of scope for `dl-consolidation`. |
| DL-36 | nm-cca2 fill (delivery review 2026-11-12): `NMCCA2.logEmit` (`PublicKey/NonMalleability/Indistinguishability/Forward.lean`) generalizes `Games.EffFill.relabelN`/`relabel` (`Games/Efficiency/OracleBridge.lean`), and its log facts `logEmit_encodeLog`, `iterate_pairSndD_encodeLog`, `flatMap_range_drop`, `length_le_length_encodeLog`, `length_iterate_pairSndD_le`, `polyTimeComputable_logEmit` mirror `relabelN_encodeHist`, `length_le_length_encodeHist` and the orbit bound of `bridgePre_poly` (undisclosed); public `finU`, `finZ`, `finW`, `finA`, `finL`, `fields_finInput` are the DL-34 round-input readers (`rU`…`rL`) again; `ofFn_nthCt` (owned file) is DL-34's generic block fact (`ofFn_acTapes`, `ofFn_pkTapes`); the private readers `rState`…`rAns` (disclosed). Promotion requests: `fwdHandler`/`fwdHandler_impl`, `exists_withAdviceOn` (→ `Games/Efficiency`), `cntRead`/`ansRead` (→ `BitCodec`), `indImpl_eq_of_msgLen_eq_zero` (→ `PublicKey/OracleSecurity`, after that file is split: it is at 999 lines). | several | **Paid** ([#299](https://github.com/Shilun-Allan-Li/tcslib/pull/299), merge `eff2dcd0`, 2026-11-14; Gate 21) | After the DL-30–DL-34 consolidation lands: put `logEmit` beside `relabelN` with `relabel x = logEmit relabelEmit x`; re-point `dCnt`/`dCt`/`dIn`/`dFin`/`eBit`/`eMsg`/`eTape`/`eCt` to R6's readers and delete `finU`…`fields_finInput`; derive `ofFn_nthCt` from the generic block lemma; promote the accepted requests. |
| DL-37 | nm-sim fill (delivery review 2026-11-13; **undisclosed**, accepted as debt by Seyoon 2026-11-13): `NMSim.chunkAt`/`chunkAt_eq`/`length_chunkAt` (`PublicKey/NonMalleability/Simulation/Hybrid.lean`) and the block lemmas `ofFn_block`, `chunkAt_flatten_append`, `map_chunkAt_flatten`; private `padFin_replicate_false` (`Simulation/Challenge.lean`); `Rounds.impl_of_ret`, `rdU`…`rdLog`/`rdState`, `rdAns`, `Simulator.finSt` (`Simulation/Rounds.lean`, `Simulator.lean`); also generic neighbours `expect_eq_until_bad`, `NMSim.expect_simulate_eager`, `expect_congr_of_allOutputs`, `chunkMap`; disclosed: `flatMap_range_drop`, `ofFn_padFin_eq_padL`, `polyTimeComputable_guessBit`, `ofFn_eq_map_range` | `coinBlock`/`coinBlock_eq`/`length_coinBlock` (`Asymptotic/Adversary.lean`), `OneWayLemmas.ofFn_block_eq_take_drop`, `NMCCA2.ofFn_nthCt`, Lamport `coinBlock_flatten`; `PRFGame.padFin_replicate_false` (`OracleFromPRF/Transfer.lean`; → `Games.padFin_replicate_false` in the consolidation); DL-34 private `impl_of_ret` (`AdaptiveCPA/Handler.lean`, `PRFGame`) and readers `rU`…`rL`/`rS`; `Games.prob_eq_until_bad`, `BitwiseSim.expect_simulate_eager`, `ProbComp.expect_mono_of_allOutputs`, `relabelN`/`logEmit` (DL-36); ZK `ofFn_eq_map_range` ×2; A4 `EnsembleLemmas.ofFn_padFin_eq_padL`; `rFwd`/`rY`/Forward `rAns` | **Paid** ([#299](https://github.com/Shilun-Allan-Li/tcslib/pull/299), merge `eff2dcd0`, 2026-11-14; Gate 21) | Landing of the consolidation (after nm-sim): delete the private `padFin_replicate_false` and use `Games.padFin_replicate_false`; re-point the nm-sim files to the moved names. Post-consolidation fold window, with DL-36: fold `chunkAt` onto `coinBlock` (58 uses) and place the block lemmas beside it; re-point `rdU`…`rdLog`, `rdState`, `finSt` to `InteractiveHandler.rU`…`rS` and `impl_of_ret` to `InteractiveHandler.impl_of_ret`; derive `prob_eq_until_bad` and `ChallengeSim.expect_simulate_eager` from the general nm-sim forms; one iterate-and-emit definition for `relabelN`/`logEmit`/`chunkMap`; merge the three `ofFn_eq_map_range` into `Foundations/BitLists`; make `NMSim.ofFn_padFin_eq_padL` the A4 lemma; fold `rdAns` with the `rFwd`/`rY`/`rAns` readers; promote the accepted requests (review r1 table). |
| DL-38 | dl-folds fill (worker REPORT §0.6, disclosed; delivery review 2026-11-14): inline re-proofs of `impl_of_query` (`acHandler_impl_forward`) and of a returning finalization (`pkHandler_finish`, `acHandler_finish`); a local `have` equal to `polyTimeComputable_ansRead` (`OracleFromPRF.lean`); further block-window restatements (`Primality.ofFn_chunk`, `ColRep.drop_take_ofFn_blockRead`, `Factoring.fac_ofFn_halves`, already corollaries); other iterate-and-emit loops (`BlockEncryptor`, `EnsembleLemmas.CopiesLoop`, `StretchMachine`, `CommitmentLemmas.ComLoop`, ZK `EncodingMachines`); the ZK pair `GI.iterate_pairSndD_encodeMsgs` / `ColMachines.iterate_pairSndD_encodeMsgs`; and the B3 `blocks` aliases (`EnsembleLemmas.blocks` and its lemmas, private `Ensembles.blocks`), escalated. | `InteractiveHandler.impl_of_query`, `finish_of_ret`; `Games.polyTimeComputable_ansRead`; `FunFamily.ofFn_blocks`; `Games.iterEmit`; `FunFamily.blocks` | Open (deferred) | Opportunistic: fold each when its file is next touched. The B3 aliases need a gate-approved restatement of `exists_copiesRed`, `ofFn_blocks_symm`, `take_drop_ofFn_blocks`, `ComLoop.emit_init_of_lt` and of the bodies of `PRFGame.pkTapes`, `Ensemble.copies` (all definitionally equal). Complexity copies of `ofFn_eq_map_range` and `flatMap_range_drop` are another campaign's. |
| DL-39 | ext-nosrc fill (worker request and delivery review 2026-11-14, disclosed): `Randomness.Rejection.tupleEquiv` restates Mathlib's `(Fin.consEquiv _).symm`; generic `FinDist` facts local to `Randomness/Extraction/Rejection.lean` (`sum_map`, `expect_map`, `probTrue_map`, `probTrue_le_one`, `probTrue_nonneg`, `map_map`, `map_prod_snd`, `uniform_prod`, `map_uniform_equiv`, `mixture`, `mixture_isSource`, `uniform_probTrue`); no exact duplicate in TCSlib (nearest: `SamplingFinDist.uprob_comp_eq_probTrue_map`, `Experiments.uprob_comp_eq_sum_map`, `ProbComp.expect_map`). | Mathlib `Fin.consEquiv`; `InformationTheory/FinDist` (to be added) | Open (deferred) | Promote the `FinDist` facts to `InformationTheory/FinDist` and use `Fin.consEquiv` in a later job (`FinDist` was frozen for the fill). The authoritative full promotion list (also `map_apply_expect`, `branch_apply`, the uniform-machine family, `take_poly`) is the delivery's `evidence/promotion-requests.md`, `rejection-review.md`, `sampler-review.md` (exchange `a5da5cc3`, `inbox/fills/ext-nosrc/`; Gate 22 observation). |
| DL-40 | cca2-ett fill (delivery review 2026-11-14): undisclosed `ETTGame.eval_toOracleAdversary_len` (`EncryptThenTag/Machines.lean`) generalizes public `PRFGame.eval_toOracleAdversary_width` (`OracleFromPRF/Reduction.lean`, its `ℓ = n` case); disclosed `ETTGame.zipWith_xor_cancel` = four private `zipWith_xor_xor_self` copies (`FromPRF`, `FromPRG`, `SpecialEncryption`, owned `zipWith_xor_xor_self'`; public relative `zipWith_xor_cancel_left`, other orientation); Gate 23 (G23-01, Seyoon 2026-11-14: debt now, fold in cleanup): private `length_le_length_encodeLog` (`EncryptThenTag/Machines.lean`) = the private copy in `NonMalleability/Indistinguishability/Forward.lean:108`; `ETTGame.prfAdv_eq_expect` re-derives private `prfAdv_prfReduction` (public relative `prfAdv_eq`, uprob form); generic forms `ETTGame.tapeImpl`/`simulate_tapeImpl_congr`/`expect_simulate_tapeImpl` (AdaptiveCPA), `recBits` family and `ovr` (PRFGame), `expect_simulate_abs` (`Games.simulate_eq_of_abs_bounded`), private `abs_expect_sub_le_expect` (`ProbComp.abs_expect_sub_le`). | `Foundations/BitLists`, `Pseudorandom/Functions`, `Games/*`, the general ETT forms | Open (deferred) | Promote the general forms (worker requested most) and re-derive the specialised copies from them; fold the private XOR copies; publish `length_le_length_encodeLog` in `Games/Efficiency/Strings.lean` beside `length_encodeLog_le` and delete both private copies (cleanup job). |
| DL-41 | dl-crh fill (delivery review 2026-11-14): **undisclosed** `FromDiscreteLog.inputWord_split` restates `ofFn_eq_init_append` (`Asymptotic/ReductionSupport.lean`, up to `Fin.init`); `ofFn_splitBits_fst/_snd` restate `ofFn_splitCoins_fst/_snd` (`CollectionsHelpers.lean`; `Authentication.splitBits` = `splitCoins`); disclosed re-derivations from public readers of private `dlb_expo_val`, `fac_listToNat_inj`, `ofFn_splitCoins_symm_cast`, `dla_statClose_expDec`; near relatives `residueFinEquiv` (Mathlib `ZMod.finEquiv`), `boundedInputEquiv` (`Fin.snocEquiv`), `expect_sample_eq_uexp` (`Games.Bridge.prob_sample_eq_uprob`). | `ofFn_eq_init_append`, `ofFn_splitCoins_*`, a `splitBits = splitCoins` bridge; worker promotion list `evidence/PROMOTION.md` (exchange `9ad236d1`) | Open (deferred) | `inputWord_take` (Gate 24 G24-01) and `inputWord_split` re-pointed to `take_ofFn_castLE` / `ofFn_eq_init_append` by LE-reuse `d356381a` (#307); the rest: re-point and promote in a later job. |
| DL-42 | hash-sign fill (delivery review 2026-11-14): `HashSignForward.roundWord`/`handler` repeats the `Games/Forwarding` `fwdRun`/`fwdHandler` pattern with a hashed query and different widths (disclosed); `splitBits_pad_concat` is a corollary of `Games.padFin_append_split`; `expect_simulate_sample_once` near `Games.expect_simulate_eager`; `MachineCodec.ext_of_fields`, `forgerCodec_eq_bitCodec`, `eq_pure_of_cost_zero` overlap the parallel lamport delivery's `lamport_codec_ext`, `lamport_forgerCodec`, `exists_pure_of_cost_zero`. | `Games/Forwarding` (a query-map `fwdHandler`), `Games/BitCodec`, `Games/Hopping`, `Games/Machines` | Open (deferred) | Generalize `fwdHandler`; promote the codec/cost facts to `Games/Machines` (no attribute) and fold the lamport copies once both units have landed. |
| DL-43 | lamport fill (delivery review 2026-11-14): **undisclosed** `LamportFill.signatureBlock σ i` = `FunFamily.blocks n n σ i` (via `blocks_apply`; DL-9 class); near relatives `Blocks.flatten_ofFn_update` (`CommitmentLemmas.ofFn_update_eq`), `Averaging.expect_favourable_of_success` (`ProbComp` counterpart of `HardcoreBit.uprob_mul_le_uexp`). Overlaps with hash-sign are DL-42. Also the follow-up (Seyoon, 2026-11-14): restate the frozen `lamport_oneTimeSecure` hypothesis `f` over `Fin (var.eval n)` with a published reader, clearing its 16 seal-B failures. | `FunFamily.blocks`; `CommitmentLemmas`; `HardcoreBit` | Open (deferred) | Re-point `signatureBlock`; promote the averaging lemma; the frozen-statement restatement needs its own gate. |
| DL-44 | prf-mac fill (delivery review 2026-11-15): F-01 local `hadv` in `MAC/FromPRF/Bound.lean` re-proves public `ETTGame.prfAdv_eq_expect` (**ruling Seyoon 2026-11-15: promote now** to the PRF layer beside `prfAdv`, re-derive the ETT copy proof-only, re-point prf-mac); F-02 `decide_fnForge`'s `hw`/`htake`/`hdrop` restate list readings of `splitBits` (`take_ofFn_castLE`, `CollectionsHelpers.ofFn_drop_take`, `FromDiscreteLog.ofFn_splitBits_fst/_snd`); F-03 `PRFMAC.blocks`/`macState`/`hits_nil_iff` near `GGMRed.tblEnc`/`lookup` (cca2-ett `tblW`). The private `prfAdv_prfReduction` (`OracleFromPRF.lean`) is the same identity specialised (DL-40). | `PRF.prfAdv_eq_expect` (to be published); the list readers above; `GGMRed.tblEnc` | Open | F-01 by the promotion PR; F-02/F-03 and the private `prfAdv_prfReduction` in the deferred cleanup. |
| DL-45 | learning fill (delivery review 2026-11-15): undisclosed `LearnPRF.uprob_eq_point` = `OneWay.uprob_eq_one_div_card` (reversed); inline re-proof of `MultiMsg.abs_uexp_sub_le_uprob` in `abs_gameProb_random_sub_half_le` (both re-pointed by maintainer LE-reuse where the import is acyclic); private `length_blk` re-proves `MultiMsg.length_histBlock` for the disclosed private copy `blk` of `histBlock`; `flip0`/`flip0_flip0` = `flipBit`/`flipBit_flipBit` (BooleanAnalysis) and `flipAt` (DeterministicCC); `foldr_pairEncode_nil` reads `Strategy.encodeMsgs`; short-name clashes `relabel`/`relabel_eq` (DL-36 family) and `flipAt`. | `OneWay.uprob_eq_one_div_card`; `MultiMsg.abs_uexp_sub_le_uprob`, `length_histBlock`; `BooleanAnalysis.flipBit` | Open | Items 1–2 by LE-reuse at landing; the rest in the deferred cleanup. |

## ===== briefs/pass-shelat-ch5-8/maintainer/promote-prfadv-2026-11-15/pr-body.md =====

## Promote `prfAdv_eq_expect` to the PRF layer (DL-44 F-01)

Seyoon's ruling of 2026-11-15 on prf-mac finding F-01 (duplication ledger DL-44): publish the generic PRF-advantage
identity beside `prfAdv`, and re-derive the encrypt-then-tag copy from it with a proof-only change. prf-mac then
re-points its local `hadv` in `MAC/FromPRF/Bound.lean` (on its landing branch `land/pass-shelat-prf-mac`, not on
ch2-4) by a proof-only landing edit, which is not part of this PR.

**Branch:** `promote/pass-shelat-prfadv-expect` at `5757bc06`, 1 commit on `cryptography/pass-shelat-ch2-4` at `8aefdab4`
(the tip after the #311 merge).

### Changes

**`TCSlib/Cryptography/Pseudorandom/Functions/Defs.lean`**
- New theorem `TCSlib.Cryptography.prfAdv_eq_expect`, placed after `prfAdv_nonneg` in a `section Expect` that opens
  `Games ProbComp`. It has a formula docstring and a proof sketch, and no attribute:
  ```lean
  theorem prfAdv_eq_expect {K ρ : Type} [Fintype K] [Nonempty K] [Fintype I] [DecidableEq I]
      [Fintype O] [Nonempty O] [Fintype ρ] [Nonempty ρ] (F : K → I → O)
      (A : OracleAdversary ρ I O) :
      prfAdv F A =
        |expect (sample K)
            (fun k => expect (sample ρ) fun c => if (A c).eval (F k) = true then (1 : ℝ) else 0) -
          expect (sample (I → O))
            (fun R => expect (sample ρ) fun c => if (A c).eval R = true then (1 : ℝ) else 0)|
  ```
  It generalises `ETTGame.prfAdv_eq_expect` from `K = I = O = {0,1}^m` to any finite nonempty key, input, output and
  coin types. The proof is the ETT proof unchanged.
- New import `TCSlib.Cryptography.Games.Bridges.Experiments`. The proof needs `Bridge.acceptProb_eq`,
  `Bridge.acceptGame_eq`, `accept_eq`, `expect`, `sample`, `prob_bind` and `prob_pure`.
  - There is no cycle: the closure of `Games.Bridges.Experiments` (7 modules) does not contain `Defs`.
  - The import adds `Games.Probability`, `Games.Advantage` and `Games.Bridges.Experiments` to the closures of `Defs`
    and the `Pseudorandom/Functions` facade. 42 of the 95 modules downstream of `Defs` gain them. It adds nothing to
    root `TCSlib`.
  - No new module was needed, so the facade `Pseudorandom/Functions.lean` is **not** edited and nothing conflicts with
    prf-long.
- One new `## Main results` bullet.

**`TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Reduction.lean`**
- `ETTGame.prfAdv_eq_expect` is now `:= TCSlib.Cryptography.prfAdv_eq_expect Fm A'` (proof only).
- Its name and statement are unchanged. Its docstring is unchanged except for one inserted sentence: "This is the
  published `TCSlib.Cryptography.prfAdv_eq_expect` at `K = I = O = {0,1}^m`."
- Its two uses in `EncryptThenTag.lean` (`ccaScheme_cca2`) and the one in `exists_tagStep` build unchanged.

No other file changes. No prf-long-owned file is touched (`Asymptotic/Defs.lean`, the facade, `FromPRF*`).

### Checks
- **Statements.** decls2 against `8aefdab4` shows 1 ADDED (the new theorem), 0 CHANGED and 0 REMOVED. All 20
  pre-existing declaration headers of the two files are byte-identical.
- **Build.** I built with `scripts/lean_check_tree.sh`, one module at a time, with no `lake`, on a tree at the
  `eff2dcd0` base.
  - The queue was 129 modules: the 2 changed files and their downstream (96 modules with them), plus the
    #303–#309 and #311 base delta and its downstream (63), up to root `TCSlib`, `audits/garg-ch1-3/Checks` and
    `audits/pass-shelat/Checks`.
  - All 129 returned rc 0 with 0 errors.
  - The only sorries are the 10 pre-existing ones: MAC/FromPRF 1, SpecialEncryptionSecurity 3, the #311 statement
    `SpecialEncryptionMulti` 1, GarblingSecurity 1, Yao 3 and Randomness/Learning 1. Every warning was already there
    before, or is #311's own `sorry` warning.
  - Each of the 127 modules with a same-source reference build produced a byte-identical olean. The two #311 modules
    have no reference. So the new import changes no downstream olean.
- **Axioms.** `prfAdv_eq_expect`, `ETTGame.prfAdv_eq_expect`, `ETTGame.exists_tagStep` and
  `Composability.ccaScheme_cca2` each depend on `[propext, Classical.choice, Quot.sound]`.
- **Rule 10.** Seals A and B, strict and coe, pass for both changed files. The paired controls (`prfAdv`,
  `ProbComp.expect`, `uprob`, and `PolyExpr.eval` in B) come out ALL_OK in both harnesses.
- **Lint.** `campaign_style_lint.py TCSlib/Cryptography --check8b` gives 92 FAIL and 101 WARN at both the parent and
  the head, with identical FAIL and WARN lines. Max line width is 97 and 99.

Evidence: `dl-review/promote-prfadv/` (PROVENANCE.txt, SHA256SUMS), zipped as `dl-review/promote-prfadv-evidence.zip`.

### Base
The branch was cut from `99a38e3a` and rebased once, with an identical patch, onto `8aefdab4` after #311 merged;
#311's `SpecialEncryptionMulti` is downstream of `Defs` and is in the build above. The tip has since gained #312
(`711a9f4a`: `Complexity/Randomized/SeedMajority.lean` and the `Randomized` facade). #312 is outside both changed
files' closures and their downstream, except root `TCSlib` and `audits/pass-shelat/Checks`, which aggregate imports.
It causes no name clash and merges cleanly, so the branch was not rebased a second time.

### Follow-up
- prf-mac: re-point `hadv` in `Bound.exists_forgeGame_le` to `TCSlib.Cryptography.prfAdv_eq_expect` (proof-only
  landing edit, DL-44).
- Deferred (DL-40/DL-44): the private `prfAdv_prfReduction` in `OracleFromPRF.lean` is the same identity specialised.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA

## ===== briefs/pass-shelat-ch5-8/gates/30-prfadv-promote/pr-description.md =====

## Summary

This PR implements Seyoon's ruling of 2026-11-15 on prf-mac's finding F-01, which was to promote the lemma now. The `prf-mac` delivery had re-proved the public `ETTGame.prfAdv_eq_expect`, which came from cca2-ett (#306), line for line. That lemma is a generic identity, so it now lives next to `prfAdv`:

```lean
theorem TCSlib.Cryptography.prfAdv_eq_expect (F : K → I → O) (A : OracleAdversary ρ I O) :
    prfAdv F A =
      |expect (sample K) (fun k => expect (sample ρ) fun c => if (A c).eval (F k) then 1 else 0) -
        expect (sample (I → O)) (fun R => expect (sample ρ) fun c => if (A c).eval R then 1 else 0)|
```

- **Location:** `Pseudorandom/Functions/Defs.lean`, the defining file of `prfAdv`. It has a formula docstring and a proof sketch, and no `@[simp]`.
  - `Defs.lean` now imports `Games.Bridges.Experiments`. That adds no cycle and changes no downstream olean.
  - No file owned by the running `prf-long` job is touched.
- **Re-derived:** `ETTGame.prfAdv_eq_expect` (`EncryptThenTag/Reduction.lean`) is now `:= TCSlib.Cryptography.prfAdv_eq_expect Fm A'`. Its statement is byte-identical, and its uses in `ccaScheme_cca2` and `exists_tagStep` are unchanged.
- **Follow-up:** after this merges, `prf-mac` re-points its local copy to the new lemma with a proof-only landing edit.

## Checks

- **Statements:** decls2 shows 1 ADDED, 0 CHANGED and 0 REMOVED. All 20 pre-existing headers are byte-identical.
- **Build:** 129/129 rc 0 through root `TCSlib` and both `audits/*/Checks`. Only pre-existing admissions remain.
- **Axioms:** the new lemma, the ETT lemma, `exists_tagStep` and `ccaScheme_cca2` use only the standard axioms.
- **Rule 10:** seals A and B pass, strict and coe. Controls are ALL_OK.
- **Lint:** 92/101, unchanged.
- **Evidence:** `briefs/pass-shelat-ch5-8/maintainer/promote-prfadv-2026-11-15/promote-prfadv-evidence.zip`, `3c9a9f32…`.

A Codex gate follows.

---
_Generated by [Claude Code](https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA)_

## ===== briefs/pass-shelat-ch5-8/gates/30-prfadv-promote/pr.diff.txt =====

diff --git a/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Reduction.lean b/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Reduction.lean
index 729c93ee8..ae1366edd 100644
--- a/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Reduction.lean
+++ b/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Reduction.lean
@@ -341,6 +341,8 @@ theorem exists_tagReduction (A : NUPPT) (q : PolyExpr) (b : Bool) :
 in general form from the published readers): for an oracle adversary `A'` on `m`-bit strings,
 `prfAdv F A' = |𝔼_k 𝔼_c [A'(c)^{F k} = 1] − 𝔼_R 𝔼_c [A'(c)^R = 1]|`.
 
+This is the published `TCSlib.Cryptography.prfAdv_eq_expect` at `K = I = O = {0,1}^m`.
+
 **Proof sketch.** `prfAdv_def`, `distAdv_def`; each acceptance probability is an average over the
 key (resp. the function table) and the coins (`Bridge.acceptProb_eq`, `accept_eq`,
 `Bridge.acceptGame_eq`, `prob_bind`, `oracleDist_apply`, `randomFunction_apply`). -/
@@ -350,14 +352,8 @@ theorem prfAdv_eq_expect {m : ℕ} (Fm : (Fin m → Bool) → (Fin m → Bool) 
       |expect (sample (Fin m → Bool))
           (fun k => expect (sample ρ) fun c => if (A' c).eval (Fm k) = true then (1 : ℝ) else 0) -
         expect (sample ((Fin m → Bool) → (Fin m → Bool)))
-          (fun R => expect (sample ρ) fun c => if (A' c).eval R = true then (1 : ℝ) else 0)| := by
-  rw [prfAdv_def, distAdv_def, Bridge.acceptProb_eq, Bridge.acceptProb_eq, accept_eq, accept_eq,
-    Bridge.acceptGame_eq, Bridge.acceptGame_eq, prob_bind, prob_bind]
-  congr 2
-  · refine congrArg _ (funext fun k => ?_)
-    simp only [prob_bind, prob_pure, oracleDist_apply]
-  · refine congrArg _ (funext fun R => ?_)
-    simp only [prob_bind, prob_pure, oracleDist_apply, randomFunction_apply]
+          (fun R => expect (sample ρ) fun c => if (A' c).eval R = true then (1 : ℝ) else 0)| :=
+  TCSlib.Cryptography.prfAdv_eq_expect Fm A'
 
 include hE hFE in
 /-- **Step 1 of [PS10, Thm 170.4]: the tag key becomes a random function**,
diff --git a/TCSlib/Cryptography/Pseudorandom/Functions/Defs.lean b/TCSlib/Cryptography/Pseudorandom/Functions/Defs.lean
index 943726ff9..ec1c4e7f8 100644
--- a/TCSlib/Cryptography/Pseudorandom/Functions/Defs.lean
+++ b/TCSlib/Cryptography/Pseudorandom/Functions/Defs.lean
@@ -4,6 +4,7 @@ Released under Apache 2.0 license as described in the file LICENSE.
 Authors: TCSlib contributors
 -/
 import TCSlib.Cryptography.Pseudorandom.Functions.OracleAdversary
+import TCSlib.Cryptography.Games.Bridges.Experiments
 import Mathlib.Data.Fintype.Pi
 
 set_option maxHeartbeats 0
@@ -41,6 +42,8 @@ belong to the asymptotic layer; here the only resource tracked is the query boun
 
 * `prfAdv_eq`: the advantage written out as a difference of two probabilities.
 * `prfAdv_nonneg`.
+* `prfAdv_eq_expect`: the advantage as the gap between two nested expectations of the
+  game-hopping layer (`Games.ProbComp.expect`), keys or function table outside, coins inside.
 
 ## References
 
@@ -97,6 +100,39 @@ theorem prfAdv_nonneg [Fintype K] [Fintype I] [DecidableEq I] [Fintype O] [Finty
   rw [prfAdv_def, distAdv_def]
   exact abs_nonneg _
 
+section Expect
+
+open Games ProbComp
+
+/-- **The PRF advantage as expectations**: for a keyed family `F : K → I → O` and an oracle
+adversary `A` with coins in `ρ`, all finite and nonempty,
+`prfAdv F A = |𝔼_k 𝔼_c [A(c)^{F k} = 1] − 𝔼_R 𝔼_c [A(c)^R = 1]|`, where `k` is a uniform key,
+`R` a uniform random function `I → O` and `c` uniform coins ([Gar26, Definition 3.9] in the
+expectation form of the game-hopping layer).
+
+**Proof sketch.** Unfold to the distinguishing advantage of `oracleDist A` (`prfAdv_def`,
+`distAdv_def`). Each acceptance probability is the acceptance of the game that samples the seed
+(the key, resp. the function table) and then the coins (`Bridge.acceptProb_eq`, `accept_eq`,
+`Bridge.acceptGame_eq`); `prob_bind` and `prob_pure` turn the game into the nested expectation,
+and `oracleDist_apply`, `randomFunction_apply` read off the verdict. -/
+theorem prfAdv_eq_expect {K ρ : Type} [Fintype K] [Nonempty K] [Fintype I] [DecidableEq I]
+    [Fintype O] [Nonempty O] [Fintype ρ] [Nonempty ρ] (F : K → I → O)
+    (A : OracleAdversary ρ I O) :
+    prfAdv F A =
+      |expect (sample K)
+          (fun k => expect (sample ρ) fun c => if (A c).eval (F k) = true then (1 : ℝ) else 0) -
+        expect (sample (I → O))
+          (fun R => expect (sample ρ) fun c => if (A c).eval R = true then (1 : ℝ) else 0)| := by
+  rw [prfAdv_def, distAdv_def, Bridge.acceptProb_eq, Bridge.acceptProb_eq, accept_eq, accept_eq,
+    Bridge.acceptGame_eq, Bridge.acceptGame_eq, prob_bind, prob_bind]
+  congr 2
+  · refine congrArg _ (funext fun k => ?_)
+    simp only [prob_bind, prob_pure, oracleDist_apply]
+  · refine congrArg _ (funext fun R => ?_)
+    simp only [prob_bind, prob_pure, oracleDist_apply, randomFunction_apply]
+
+end Expect
+
 /-- Two samplers producing the same sample from every seed have the same acceptance
 probability. -/
 theorem acceptProb_congr [Fintype σ] [Fintype ρ] {X Y : σ → γ} (h : ∀ s, X s = Y s)

## ===== TCSlib/Cryptography/Pseudorandom/Functions/Defs.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pseudorandom.Functions.OracleAdversary
import TCSlib.Cryptography.Games.Bridges.Experiments
import Mathlib.Data.Fintype.Pi

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Keyed function families, random functions and the PRF advantage

At one fixed value of the security parameter, a function ensemble [Gar26, Definition 3.6]
is a random variable ranging over functions `I → O`. Following the concrete-layer
convention, random variables are pushforwards of uniform seeds, so an efficiently
computable ensemble [Gar26, Definition 3.8] is a *keyed family* `F : K → I → O`, sampled
by drawing a uniform key `k : K` and outputting `F k`. The random function ensemble
[Gar26, Definition 3.7] is the uniform distribution on the finite type `I → O`, sampled
by the identity.

The PRF advantage of an oracle adversary `A` [Gar26, Definition 3.9] is
`|Pr_{k,r}[A^{F_k}(r) = 1] - Pr_{R,r}[A^R(r) = 1]|`. It is the distinguishing advantage
`distAdv` of the oracle adversary viewed as a distinguisher of whole functions; the
adversary only ever sees the values at its queries, which is what makes the advantage
meaningful for bounded-query adversaries.

The efficiency conditions of Definition 3.8 (a polynomial-time key generator and
evaluator) and the quantification over non-uniform PPT adversaries of Definition 3.9
belong to the asymptotic layer; here the only resource tracked is the query bound
`OracleAdversary.BoundedBy`.

## Main definitions

* `randomFunction I O`: the sampler of a uniform random function `I → O`.
* `prfAdv F A`: the PRF advantage of the oracle adversary `A` against the keyed family `F`.

## Main results

* `prfAdv_eq`: the advantage written out as a difference of two probabilities.
* `prfAdv_nonneg`.
* `prfAdv_eq_expect`: the advantage as the gap between two nested expectations of the
  game-hopping layer (`Games.ProbComp.expect`), keys or function table outside, coins inside.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4.1, Definitions 3.6–3.9.
-/

namespace TCSlib.Cryptography

variable {K ρ σ σ' γ : Type*} {I O : Type}

/-- The sampler of a uniformly random function `I → O`: the seed is the function table
itself, a uniform element of the finite type `I → O`. This is the random function
ensemble `R_n` of [Gar26, Definition 3.7] at one value of the security parameter; its
seed has `|I| · log |O|` bits, `n · 2^n` for `I = O = {0,1}^n`. -/
def randomFunction (I O : Type*) : (I → O) → I → O := id

/-- The random-function sampler returns its seed, the function table itself:
`randomFunction I O f = f`. -/
theorem randomFunction_apply (I O : Type*) (f : I → O) : randomFunction I O f = f :=
  rfl

/-- The PRF advantage of the oracle adversary `A` against the keyed function family
`F : K → I → O` (a function ensemble [Gar26, Definitions 3.6 and 3.8], keys uniform in
`K`): `|Pr_{k,r}[A^{F_k}(r) = 1] - Pr_{R,r}[A^R(r) = 1]|` with `R` a uniform random
function, [Gar26, Definition 3.9] at one value of the security parameter. `F` is
pseudorandom when this is negligible for every efficient adversary; the concrete layer
bounds it by explicit reductions instead. -/
noncomputable def prfAdv [Fintype K] [Fintype I] [DecidableEq I] [Fintype O] [Fintype ρ]
    (F : K → I → O) (A : OracleAdversary ρ I O) : ℝ :=
  distAdv F (randomFunction I O) (oracleDist A)

/-- The defining equation of `prfAdv`: the distinguishing advantage of `oracleDist A` between
the keyed family and the random-function sampler,
`prfAdv F A = distAdv F (randomFunction I O) (oracleDist A)`. -/
theorem prfAdv_def [Fintype K] [Fintype I] [DecidableEq I] [Fintype O] [Fintype ρ]
    (F : K → I → O) (A : OracleAdversary ρ I O) :
    prfAdv F A = distAdv F (randomFunction I O) (oracleDist A) :=
  rfl

/-- The PRF advantage written out: the difference between the probability that `A`
accepts with oracle `F k` for uniform `k` and coins `r`, and the probability that it
accepts with a uniform random function `R` as oracle. [Gar26, Definition 3.9]. -/
theorem prfAdv_eq [Fintype K] [Fintype I] [DecidableEq I] [Fintype O] [Fintype ρ]
    (F : K → I → O) (A : OracleAdversary ρ I O) :
    prfAdv F A = |uprob (fun z : K × ρ => (A z.2).eval (F z.1) = true) -
      uprob (fun z : (I → O) × ρ => (A z.2).eval z.1 = true)| := by
  rw [prfAdv_def, distAdv_def, acceptProb_def, acceptProb_def]
  simp only [oracleDist_apply, randomFunction_apply]

/-- The PRF advantage is nonnegative. -/
theorem prfAdv_nonneg [Fintype K] [Fintype I] [DecidableEq I] [Fintype O] [Fintype ρ]
    (F : K → I → O) (A : OracleAdversary ρ I O) : 0 ≤ prfAdv F A := by
  rw [prfAdv_def, distAdv_def]
  exact abs_nonneg _

section Expect

open Games ProbComp

/-- **The PRF advantage as expectations**: for a keyed family `F : K → I → O` and an oracle
adversary `A` with coins in `ρ`, all finite and nonempty,
`prfAdv F A = |𝔼_k 𝔼_c [A(c)^{F k} = 1] − 𝔼_R 𝔼_c [A(c)^R = 1]|`, where `k` is a uniform key,
`R` a uniform random function `I → O` and `c` uniform coins ([Gar26, Definition 3.9] in the
expectation form of the game-hopping layer).

**Proof sketch.** Unfold to the distinguishing advantage of `oracleDist A` (`prfAdv_def`,
`distAdv_def`). Each acceptance probability is the acceptance of the game that samples the seed
(the key, resp. the function table) and then the coins (`Bridge.acceptProb_eq`, `accept_eq`,
`Bridge.acceptGame_eq`); `prob_bind` and `prob_pure` turn the game into the nested expectation,
and `oracleDist_apply`, `randomFunction_apply` read off the verdict. -/
theorem prfAdv_eq_expect {K ρ : Type} [Fintype K] [Nonempty K] [Fintype I] [DecidableEq I]
    [Fintype O] [Nonempty O] [Fintype ρ] [Nonempty ρ] (F : K → I → O)
    (A : OracleAdversary ρ I O) :
    prfAdv F A =
      |expect (sample K)
          (fun k => expect (sample ρ) fun c => if (A c).eval (F k) = true then (1 : ℝ) else 0) -
        expect (sample (I → O))
          (fun R => expect (sample ρ) fun c => if (A c).eval R = true then (1 : ℝ) else 0)| := by
  rw [prfAdv_def, distAdv_def, Bridge.acceptProb_eq, Bridge.acceptProb_eq, accept_eq, accept_eq,
    Bridge.acceptGame_eq, Bridge.acceptGame_eq, prob_bind, prob_bind]
  congr 2
  · refine congrArg _ (funext fun k => ?_)
    simp only [prob_bind, prob_pure, oracleDist_apply]
  · refine congrArg _ (funext fun R => ?_)
    simp only [prob_bind, prob_pure, oracleDist_apply, randomFunction_apply]

end Expect

/-- Two samplers producing the same sample from every seed have the same acceptance
probability. -/
theorem acceptProb_congr [Fintype σ] [Fintype ρ] {X Y : σ → γ} (h : ∀ s, X s = Y s)
    (D : γ → ρ → Bool) : acceptProb X D = acceptProb Y D := by
  rw [funext h]

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Reduction.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Handler
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Machines
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Reduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The tag-key PRF reduction for the encrypt-then-tag scheme

The reduction of [PS10, Theorem 170.4], step 1, as a next-query oracle machine at parameter `2n`:
the budget cap of the adversary (`exists_capMachine`), the input-free companion
(`Games.exists_toCompOn_of_toComp`), T2 (`Games.exists_interactiveHandlerMachine`) applied to the
handler `dHandler` with the budget `q(2n)`, T4 (`Games.exists_toOracleAdversary_of_bitCodec`) at
the length `2n`, and the parameter halving (`exists_halfMachine`). Its acceptance probability at
parameter `2n` against any function `g` on `2n` bits is the acceptance probability of the CCA2
experiment with `f_{k₁}` and `g` (`exists_tagReduction`).

The proof answers the handler's outer queries by `g` (`gOuter`) and composes the two
implementations (`QueryImpl.comp`). Each composed call, from the encoded state `dState j o`, is the
call of `ettTape` from `((o, T), j)` with the handler's tapes in advance (`comp_dAbs`), as long as
`j` is below the number `q(2n)` of tapes; the capped adversary asks at most `q(n) ≤ q(2n)` queries,
so this holds along every run (`Games.simulate_eq_of_abs_bounded`). Drawing the seed uniformly
gives the key and fresh nonces (`expect_ettTape`).

## Main definitions

* `ETTGame.gOuter`: the outer oracle answering with `g`.
* `ETTGame.dAbs`: the handler's state as a function of `ettTape`'s state.

## Main results

* `ETTGame.comp_dAbs`: one composed call is a call of `ettTape`.
* `ETTGame.exists_tagReduction`: the reduction.
* `ETTGame.prfAdv_eq_expect`: the PRF advantage as expectations.
* `ETTGame.exists_tagStep`: step 1, the gap to the random tag function is a PRF advantage at `2n`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 170.4 (book p. 170).
-/

namespace TCSlib.Cryptography.Composability.ETTGame

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

/-! ### The outer oracle and the composed calls -/

/-- **The outer oracle answering with `g`:** a query `x` is answered `g x`, lengths adjusted,
`gOuter n g i x s = pure (padFin _ ⟦g (padFin (2n) ⟦x⟧)⟧, s)`. -/
noncomputable def gOuter (n : ℕ) (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) :
    QueryImpl (bitSpecAt tagOut tagOut n) Unit unifSpec :=
  QueryImpl.ofComp fun _ x => .pure (padFin _ (List.ofFn (g (padFin (2 * n) (List.ofFn x)))))

/-- `gOuter n g i x s = pure (padFin _ ⟦g (padFin (2n) ⟦x⟧)⟧, s)`. -/
theorem gOuter_apply (n : ℕ) (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)) (i : Fin 1)
    (x : (bitSpecAt tagOut tagOut n).dom i) (s : Unit) :
    gOuter n g i x s = .pure (padFin _ (List.ofFn (g (padFin (2 * n) (List.ofFn x)))), s) := by
  rw [gOuter, QueryImpl.ofComp_apply, OracleComp.pure_bind]

section Composed

variable (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
  (E : List Bool → List Bool) (hE : PolyTimeComputable E)
  (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (F n s x))
  (q : PolyExpr) (b : Bool) (n : ℕ) (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))
  (z : List Bool) (k : Fin n → Bool) (W : Fin (q.eval n * n) → Bool)

/-- The handler's state and the (trivial) outer state, as functions of `ettTape`'s state:
`dAbs … (σ, j) = (dHState q E hE b n j σ.1, ())`. -/
def dAbs (s : St n (ettCt.eval n) × ℕ) :
    (Fin ((dHandler q E hE b).stateLen.eval n) → Bool) × Unit :=
  (dHState q E hE b n s.2 s.1.1, ())

/-- `dAbs E hE q b n s = (dHState q E hE b n s.2 s.1.1, ())`. -/
theorem dAbs_eq (s : St n (ettCt.eval n) × ℕ) :
    dAbs E hE q b n s = (dHState q E hE b n s.2 s.1.1, ()) :=
  rfl

/-- The tapes of the tape word, extended to every index (`AdaptiveCPA.extTape`):
`dTapes q n W = extTape (blocks (q n) n W)`. -/
noncomputable def dTapes : ℕ → Fin n → Bool :=
  AdaptiveCPA.extTape (EnsembleLemmas.blocks (q.eval n) n W)

/-- `dTapes q n W = extTape (blocks (q n) n W)`. -/
theorem dTapes_eq : dTapes q n W = AdaptiveCPA.extTape (EnsembleLemmas.blocks (q.eval n) n W) :=
  rfl

/-- Below `q(n)`, the extended tapes are the tapes: `dTapes q n W j = dTape q n W j hj`. -/
theorem dTapes_of_lt (j : ℕ) (hj : j < q.eval n) : dTapes q n W j = dTape q n W j hj := by
  rw [dTapes_eq, AdaptiveCPA.extTape_of_lt _ hj, dTape_eq]

/-- Reading the answer of `g` to a pair `r ‖ c₁` with `|r| = |c₁| = n` through the outer oracle:
`⟦padFin _ ⟦g (padFin (2n) ⟦padFin _ (r ++ c₁)⟧)⟧⟧ = tagL g r c₁`. -/
private theorem gOuter_pair {r c : List Bool} (hr : r.length = n) (hc : c.length = n) :
    List.ofFn (padFin ((tagOut 0).eval n) (List.ofFn (g (padFin (2 * n)
      (List.ofFn (padFin ((tagOut 0).eval n) (r ++ c))))))) = tagL g r c := by
  have h2 : (tagOut 0).eval n = 2 * n := by rw [tagOut_eq, tagLen_eval]
  have e1 : List.ofFn (padFin ((tagOut 0).eval n) (r ++ c)) = r ++ c :=
    ofFn_padFin_of_length (by rw [List.length_append, hr, hc, h2]; omega)
  rw [e1, ofFn_padFin_of_length (by rw [List.length_ofFn, h2]), tagL_eq, pairV_eq]

include hFE in
/-- **One composed call is a call of `ettTape` with the tapes in advance:** from the encoded state
`dState j o` with `j < q(n)`, the handler composed with `gOuter g` answers as `ettTape` with pad
function `f_k` and tag function `g` and the tapes `dTapes W` from `((o, T), j)`, both
deterministic, with the new state abstracted; the counter grows by one.

**Proof sketch.** By the oracle, the record, the refusal test and well-formedness: encryption and a
first challenge ask `g` at `r ‖ c₁` (`dHandler_impl_enc`, `dHandler_impl_challenge_none`); a
well-formed decryption that is not refused asks `g` at its pair (`dHandler_impl_dec_wf`); the
other calls answer directly. The outer oracle answers `g` (`gOuter_apply`, `gOuter_pair`), and the
answers are `ettStep`'s (`ettStep_enc`, …, `decAnsW_eq`). -/
theorem comp_dAbs (i : Fin 3) (x : (bitSpecAt ettDin ettDout n).dom i)
    (s : St n (ettCt.eval n) × ℕ) (hs : s.2 < q.eval n) :
    ∃ (y : (bitSpecAt ettDin ettDout n).rng i) (s' : St n (ettCt.eval n) × ℕ),
      ettTape (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n (F n k)
          g b (dTapes q n W) i x s = .pure (y, s') ∧ s'.2 ≤ s.2 + 1 ∧
      (gOuter n g).comp ((dHandler q E hE b).impl n z (dHSeed q E hE b n (k, W))) i x
          (dAbs E hE q b n s) = .pure (y, dAbs E hE q b n s') := by
  obtain ⟨⟨o, T⟩, j⟩ := s
  have hj : j < q.eval n := hs
  refine ⟨(ettStep (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
      (F n k) g false b (dTapes q n W j) i x (o, T)).1,
    ((ettStep (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
      (F n k) g false b (dTapes q n W j) i x (o, T)).2, j + 1),
    ettTape_apply (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
      (F n k) g b (dTapes q n W) i x (o, T) j, le_rfl, ?_⟩
  rw [dTapes_of_lt q n W j hj, QueryImpl.comp_apply, dAbs_eq]
  simp only
  match i, x with
  | 0, x =>
    have hx : (List.ofFn x).length = n := by
      rw [List.length_ofFn]
      show (ettDin 0).eval n = n
      rw [ettDin_zero, PolyExpr.eval_var]
    rw [dHandler_impl_enc q E hE b F hFE n z k W x j o hj, simulate_query, gOuter_apply,
      OracleComp.pure_bind, simulate_pure, OracleComp.pure_bind, ettStep_enc, dAbs_eq,
      gOuter_pair n g List.length_ofFn (length_maskL (F n k) _ hx), ← encW_eq]
  | 1, x =>
    rw [ettStep_dec, decAnsW_eq]
    by_cases href : refW o (List.ofFn x) = true
    · rw [dHandler_impl_dec_ref q E hE b n z k W x j o hj href, simulate_pure,
        OracleComp.pure_bind, dAbs_eq]
      simp only [href, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false]
    · rw [Bool.not_eq_true] at href
      by_cases hwf : wfW n (List.ofFn x) = true
      · have hwf' := hwf
        rw [wfW_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hwf'
        rw [dHandler_impl_dec_wf q E hE b F hFE n z k W x j o hj href hwf, simulate_query,
          gOuter_apply, OracleComp.pure_bind, simulate_pure, OracleComp.pure_bind, dAbs_eq,
          gOuter_pair n g hwf'.1 hwf'.2, validW_eq, hwf, href]
        simp only [Bool.not_false, Bool.true_and, Bool.true_or, Bool.and_true, decide_eq_true_eq]
        by_cases ht : tagL g (wR (List.ofFn x)) (wC (List.ofFn x)) = wT (List.ofFn x)
        · rw [if_pos ht, if_pos ht.symm]
        · rw [if_neg ht, if_neg (Ne.symm ht)]
      · rw [Bool.not_eq_true] at hwf
        rw [dHandler_impl_dec_nwf q E hE b n z k W x j o hj href hwf, simulate_pure,
          OracleComp.pure_bind, dAbs_eq, validW_eq, hwf]
        simp only [Bool.false_and, Bool.and_false, Bool.false_eq_true, if_false]
  | 2, x =>
    cases o with
    | some c =>
      rw [dHandler_impl_challenge_some q E hE b n z k W x j c hj, simulate_pure,
        OracleComp.pure_bind, ettStep_challenge_some, dAbs_eq]
    | none =>
      have hmsg : (AdaptiveCPA.msgOf n b (List.ofFn x)).length = n := by
        have hx : (List.ofFn x).length = n + n := by
          rw [List.length_ofFn]
          show (ettDin 2).eval n = n + n
          rw [ettDin_two, PolyExpr.eval_add, PolyExpr.eval_var]
        rw [AdaptiveCPA.msgOf_eq]
        cases b <;> simp [hx]
      rw [dHandler_impl_challenge_none q E hE b F hFE n z k W x j hj, simulate_query,
        gOuter_apply, OracleComp.pure_bind, simulate_pure, OracleComp.pure_bind,
        ettStep_challenge_none, dAbs_eq,
        gOuter_pair n g List.length_ofFn (length_maskL (F n k) _ hmsg), ← encW_eq]

end Composed

/-! ### The reduction -/

/-- The budget `q(2n)` of the handler's adversary: `(q.subst tagLen).eval n = q(2n)`. -/
theorem eval_subst_tagLen (q : PolyExpr) (n : ℕ) : (q.subst tagLen).eval n = q.eval (2 * n) := by
  rw [PolyExpr.eval_subst, tagLen_eval]

/-- **The experiment does not see the output width:** for `d = d'`, the expected first output bit
of the run through `bitCodec ins outs d` and through `bitCodec ins outs d'` agree.

**Proof sketch.** Substitute `d = d'`. -/
theorem expect_ettImpl_outLen {ins outs : Fin 3 → ℕ} {c n : ℕ} {d d' : ℕ} (hd : d = d')
    (f : (Fin n → Bool) → (Fin n → Bool)) (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))
    (rej b : Bool) (A : NUPPT) (Q : ℕ) (r : A.Coins n) :
    expect (simulate (ettImpl ins outs c n f g rej b) (A.toComp (bitCodec ins outs d) n Q r)
        (none, [])) (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) =
      expect (simulate (ettImpl ins outs c n f g rej b) (A.toComp (bitCodec ins outs d') n Q r)
        (none, [])) (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
  subst hd
  rfl

section Reduction

variable (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
  (E : List Bool → List Bool) (hE : PolyTimeComputable E)
  (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (F n s x))

include hE hFE in
/-- **The tag-key PRF reduction** [PS10, Theorem 170.4, step 1]: for a machine adversary `A` with
budget `q` and a challenge bit `b`, there is a next-query machine `D` such that, at every `n` and
for every function `g` on `2n` bits, `D` at parameter `2n` with budget `q(2n)` accepts against `g`
with the probability that `A` outputs `1` in the CCA2 experiment with `f_k` (`k` a uniform `n`-bit
key) and `g` in place of `f_{k₂}` (the oracles `ettImpl … false b`, on the lengths `ettDin`,
`ettDout`):
`𝔼_c [D^g(2n; c) = 1] = 𝔼_k 𝔼_r 𝔼[⟦A's output⟧₀ = 1 | simulate (ettImpl … f_k g false b) (A …) ∅]`.

**Proof sketch.** `D` is the halving (`exists_halfMachine`) of T4 at length `2n` applied to T2's
machine `B` for `dHandler` with budget `q(2n)` and the input-free companion of the capped adversary
(`exists_capMachine`). Its coins at `2n` are, through the halving and the bijections of T4, T2, the
companion and the cap, a seed `(k, W)` and `A`'s coins `r` (`expect_sample_equiv`,
`ChallengeSim.expect_sample_prod`, `expect_sample_comm`). For fixed seed and coins, T4 and T2 turn
`D`'s run against `g` into the evaluation, with `g`, of the reduction; evaluation is simulation
with `gOuter g` (`simulate_ofComp_pure`), which composes with the handler (`simulate_bind`,
`simulate_comp`, `dHandler_finish`); along the adversary's run (at most `q(2n)` queries) the
composite is `ettTape` with the tapes of `W` (`simulate_eq_of_abs_bounded`, `comp_dAbs`). Drawing
`W` uniformly gives fresh nonces (`expect_ettTape`), and the capped adversary at budget `q(2n)` is
`A` at budget `q(n)` (`exists_capMachine`). Widths are transported by
`eval_toOracleAdversary_len`, `PRFGame.ofFn_evalFn_toCompOn` and `expect_ettImpl_outLen`. -/
theorem exists_tagReduction (A : NUPPT) (q : PolyExpr) (b : Bool) :
    ∃ D : NUPPT, ∀ (n : ℕ) (g : (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool)),
      expect (sample (D.Coins (2 * n)))
          (fun c =>
            if (D.toOracleAdversary (2 * n) (2 * n) (2 * n) (q.eval (2 * n)) c).eval g = true
            then (1 : ℝ) else 0) =
        expect (sample (Fin n → Bool)) fun k => expect (sample (A.Coins n)) fun r =>
          expect (simulate (ettImpl (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
              (ettCt.eval n) n (F n k) g false b)
              (A.toComp (bitCodec (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) 1) n
                (q.eval n) r) (none, []))
            (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
  obtain ⟨A₁, hA₁c, hA₁⟩ := exists_capMachine A q
  obtain ⟨A₂, -, hA₂⟩ := exists_toCompOn_of_toComp A₁
  obtain ⟨B, hB⟩ := exists_interactiveHandlerMachine A₂ (q.subst tagLen) ettDin ettDout tagOut
    tagOut (.const 1) (dHandler (q.subst tagLen) E hE b)
  obtain ⟨B', -, hB'⟩ := exists_toOracleAdversary_of_bitCodec B tagLen tagLen
  obtain ⟨D, hD⟩ := exists_halfMachine B'
  refine ⟨D, fun n g => ?_⟩
  obtain ⟨φ₀, hφ₀⟩ := hA₂ n
  obtain ⟨φ₂, hφ₂⟩ := hB n
  obtain ⟨φ₄, hφ₄⟩ := hB' n
  have hq₂ : (q.subst tagLen).eval n = q.eval (2 * n) := eval_subst_tagLen q n
  have hQ : (q.subst tagLen).eval n * (dHandler (q.subst tagLen) E hE b).perCall.eval n +
      (dHandler (q.subst tagLen) E hE b).finCall.eval n = q.eval (2 * n) := by
    rw [dHandler_perCall, dHandler_finCall, PolyExpr.eval_const, PolyExpr.eval_const, hq₂]
    ring
  have hout : (dHandler (q.subst tagLen) E hE b).outLen.eval n = 1 := by
    rw [dHandler_outLen, PolyExpr.eval_const]
  have hle : q.eval n ≤ (q.subst tagLen).eval n := by
    rw [hq₂]
    exact q.eval_mono (by omega)
  -- `D`'s coins at `2n` are `B'`'s at `n`, then a seed and `A`'s coins.
  rw [hD n (2 * n) (2 * n) (q.eval (2 * n)) g, ← expect_sample_equiv φ₄, ← expect_sample_equiv φ₂,
    ChallengeSim.expect_sample_prod, expect_sample_comm, ← expect_sample_equiv φ₀,
    ← expect_sample_equiv (NUPPT.coinsCongr hA₁c n)]
  conv_rhs => rw [expect_sample_comm]
  refine congrArg _ (funext fun r => ?_)
  rw [← expect_sample_equiv (dHSeed (q.subst tagLen) E hE b n), ChallengeSim.expect_sample_prod]
  refine congrArg _ (funext fun k => ?_)
  -- One run of `D` is the reduction evaluated with `g`.
  have hrun : ∀ W : Fin ((q.subst tagLen).eval n * n) → Bool,
      (if (B'.toOracleAdversary n (2 * n) (2 * n) (q.eval (2 * n))
          (φ₄ (φ₂ (dHSeed (q.subst tagLen) E hE b n (k, W),
            φ₀ (NUPPT.coinsCongr hA₁c n r))))).eval g = true then (1 : ℝ) else 0) =
      expect (simulate (ettTape (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
          (ettCt.eval n) n (F n k) g b (dTapes (q.subst tagLen) n W))
          (A₂.toCompOn (bitCodec (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
            ((PolyExpr.const 1).eval n)) n ((q.subst tagLen).eval n) []
            (φ₀ (NUPPT.coinsCongr hA₁c n r))) ((none, []), 0))
        (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
    intro W
    have key : ∀ v : Fin 1 → Bool, (if v 0 = true then (1 : ℝ) else 0) =
        if (List.ofFn v).headD false = true then 1 else 0 := fun v => by
      rw [headD_ofFn_one]
    have h2 : _ = B.toCompOn (bitCodec (fun _ : Fin 1 => tagLen.eval n)
        (fun _ => tagLen.eval n) ((dHandler (q.subst tagLen) E hE b).outLen.eval n)) n
        ((q.subst tagLen).eval n * (dHandler (q.subst tagLen) E hE b).perCall.eval n +
          (dHandler (q.subst tagLen) E hE b).finCall.eval n)
        [] (φ₂ (dHSeed (q.subst tagLen) E hE b n (k, W), φ₀ (NUPPT.coinsCongr hA₁c n r))) :=
      hφ₂ [] (dHSeed (q.subst tagLen) E hE b n (k, W)) (φ₀ (NUPPT.coinsCongr hA₁c n r))
    rw [eval_toOracleAdversary_len B' n _ _ (tagLen_eval n), hφ₄, ← hQ, key,
      PRFGame.ofFn_evalFn_toCompOn hout.symm B n _ [] _, ← h2, dHandler_advInput]
    have hev : simulate (gOuter n g) ((simulate ((dHandler (q.subst tagLen) E hE b).impl n []
        (dHSeed (q.subst tagLen) E hE b n (k, W)))
        (A₂.toCompOn (bitCodec (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
          ((PolyExpr.const 1).eval n)) n ((q.subst tagLen).eval n) []
          (φ₀ (NUPPT.coinsCongr hA₁c n r)))
        ((dHandler (q.subst tagLen) E hE b).init n)).bind
        (fun res => (dHandler (q.subst tagLen) E hE b).finish n []
          (dHSeed (q.subst tagLen) E hE b n (k, W)) res.2 res.1)) () = _ :=
      simulate_ofComp_pure _ _ _
    have h1 := congrArg (fun c => expect c
      (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0)) hev
    simp only [expect_pure] at h1
    refine h1.symm.trans ?_
    rw [simulate_bind, simulate_comp, OracleComp.bind_assoc, expect_bind]
    simp only [OracleComp.pure_bind, dHandler_finish, simulate_pure, expect_pure]
    rw [dHandler_init_hstate, show (dHState (q.subst tagLen) E hE b n 0 none, ()) =
        dAbs E hE (q.subst tagLen) b n ((none, []), 0) from
          (dAbs_eq E hE (q.subst tagLen) b n ((none, []), 0)).symm,
      simulate_eq_of_abs_bounded _ _ (dAbs E hE (q.subst tagLen) b n) (fun s => s.2)
        ((q.subst tagLen).eval n)
        (fun i x s hs => comp_dAbs F E hE hFE (q.subst tagLen) b n g [] k W i x s hs) _
        ((q.subst tagLen).eval n) (A₂.toCompOn_costBoundedBy _ n _ _ _) ((none, []), 0)
        (Nat.zero_add _).le,
      expect_bind]
    simp only [expect_pure]
    refine congrArg _ (funext fun p => ?_)
    rw [ofFn_padFin_of_length (by rw [List.length_ofFn, dHandler_outLen])]
  simp only [hrun, dTapes_eq]
  rw [expect_sample_equiv (EnsembleLemmas.blocks ((q.subst tagLen).eval n) n) (fun T =>
      expect (simulate (ettTape (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
          (ettCt.eval n) n (F n k) g b (AdaptiveCPA.extTape T))
          (A₂.toCompOn (bitCodec (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n)
            ((PolyExpr.const 1).eval n)) n ((q.subst tagLen).eval n) []
            (φ₀ (NUPPT.coinsCongr hA₁c n r))) ((none, []), 0))
        (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0)),
    expect_ettTape _ _ _ _ _ _ _ ((q.subst tagLen).eval n)
      (fun a => if (List.ofFn a).headD false = true then (1 : ℝ) else 0) _
      ((q.subst tagLen).eval n) (A₂.toCompOn_costBoundedBy _ n _ _ _) (none, []) 0 (by omega),
    hφ₀, hA₁ n _ _ _ _ _ hle]
  exact expect_ettImpl_outLen (PolyExpr.eval_const 1 n) _ _ _ _ A _ r

/-- **The PRF advantage as expectations** (PRFGame overlap: `prfAdv_prfReduction`, re-derived here
in general form from the published readers): for an oracle adversary `A'` on `m`-bit strings,
`prfAdv F A' = |𝔼_k 𝔼_c [A'(c)^{F k} = 1] − 𝔼_R 𝔼_c [A'(c)^R = 1]|`.

This is the published `TCSlib.Cryptography.prfAdv_eq_expect` at `K = I = O = {0,1}^m`.

**Proof sketch.** `prfAdv_def`, `distAdv_def`; each acceptance probability is an average over the
key (resp. the function table) and the coins (`Bridge.acceptProb_eq`, `accept_eq`,
`Bridge.acceptGame_eq`, `prob_bind`, `oracleDist_apply`, `randomFunction_apply`). -/
theorem prfAdv_eq_expect {m : ℕ} (Fm : (Fin m → Bool) → (Fin m → Bool) → (Fin m → Bool))
    {ρ : Type} [Fintype ρ] [Nonempty ρ] (A' : OracleAdversary ρ (Fin m → Bool) (Fin m → Bool)) :
    prfAdv Fm A' =
      |expect (sample (Fin m → Bool))
          (fun k => expect (sample ρ) fun c => if (A' c).eval (Fm k) = true then (1 : ℝ) else 0) -
        expect (sample ((Fin m → Bool) → (Fin m → Bool)))
          (fun R => expect (sample ρ) fun c => if (A' c).eval R = true then (1 : ℝ) else 0)| :=
  TCSlib.Cryptography.prfAdv_eq_expect Fm A'

include hE hFE in
/-- **Step 1 of [PS10, Thm 170.4]: the tag key becomes a random function**,
`∃ D, ∀ n, |𝔼_{k₁} 𝔼_{k₂} ettAcc … (F n k₁) (F (2n) k₂) false b A (q n) -
𝔼_{k₁} 𝔼_R ettAcc … (F n k₁) R false b A (q n)| =
prfAdv (F (2n)) (D.toOracleAdversary (2n) (2n) (2n) (q (2n)))`.
For a machine adversary `A` with budget `q` and a challenge bit `b` there is a next-query machine
`D` such that at
every `n` the gap between the experiments with the tag functions `f_{k₂}` (`k₂` a uniform `2n`-bit
key) and a uniform random function on `2n` bits, the pad function being `f_{k₁}`, is the PRF
advantage of `D` at parameter `2n` with budget `q(2n)`.

**Proof sketch.** `exists_tagReduction` gives `D` and its acceptance probability against every `g`;
`prfAdv_eq_expect` writes the advantage as the gap between the averages over `k₂` and over the
function table; exchange the averages with the key `k₁` (`expect_sample_comm`). -/
theorem exists_tagStep (A : NUPPT) (q : PolyExpr) (b : Bool) :
    ∃ D : NUPPT, ∀ n : ℕ,
      |(expect (sample (Fin n → Bool)) fun k => expect (sample (Fin (2 * n) → Bool)) fun k₂ =>
          ettAcc (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
            (F n k) (F (2 * n) k₂) false b A (q.eval n)) -
        (expect (sample (Fin n → Bool)) fun k =>
          expect (sample ((Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))) fun R =>
            ettAcc (fun i => (ettDin i).eval n) (fun i => (ettDout i).eval n) (ettCt.eval n) n
              (F n k) R false b A (q.eval n))| =
        prfAdv (F (2 * n)) (D.toOracleAdversary (2 * n) (2 * n) (2 * n) (q.eval (2 * n))) := by
  obtain ⟨D, hD⟩ := exists_tagReduction F E hE hFE A q b
  refine ⟨D, fun n => ?_⟩
  rw [prfAdv_eq_expect]
  simp only [hD n, ettAcc_eq]
  rw [expect_sample_comm (α := Fin n → Bool) (β := Fin (2 * n) → Bool),
    expect_sample_comm (α := Fin n → Bool) (β := (Fin (2 * n) → Bool) → (Fin (2 * n) → Bool))]

end Reduction

end TCSlib.Cryptography.Composability.ETTGame

## ===== TCSlib/Cryptography/Games/Bridges/Experiments.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Advantage
import TCSlib.Cryptography.Foundations.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bridge: the concrete layer's experiments are games

The concrete security layer of the ch. 2–4 development measures its experiments with `uprob`,
the probability that a uniformly random element of a finite type satisfies an event. Its four
experiments are inversion (`invProb`), prediction (`predProb`), acceptance (`acceptProb`) and
distinguishing (`distAdv`). This file shows that each is the probability of a one-line game of the
`Games` framework: sample the seed and the adversary's coins, run the adversary, test. So every
concrete-layer result stated through these quantities transfers to the framework unchanged.

The basic fact is `prob_sample_eq_uprob`: sampling a finite type and testing an event has
probability `uprob` of the event. It reads `uprob` only through its published equation
`uprob_eq_card_filter`. Sampling a pair one component at a time is sampling the product
(`prob_sample_pair`), so the games may sample the seed and the coins in sequence.

The four experiments are read through their published defining equations (`invProb_def`,
`predProb_def`, `acceptProb_def`, `distAdv_def` in `Foundations/Experiments.lean`).

## Main definitions

* `Games.Bridge.acceptGame X D`: the acceptance game of a sampler and a distinguisher.

## Main results

* `Games.Bridge.prob_sample_eq_uprob`: `Pr[x ← $ α : p x] = uprob p`.
* `Games.Bridge.prob_sample_pair`: sampling `α` then `β` is sampling `α × β`.
* `Games.Bridge.invProb_eq`, `predProb_eq`, `acceptProb_eq`, `distAdv_eq`: the four concrete
  experiments as games.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley, draft of
  22 January 2026, Definitions 2.1, 2.3, 3.2–3.4 (the experiments).
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), and simulation of oracles by
  stateful handlers with query logging (`SimSemantics/`, `QueryTracking/LoggingOracle`).
-/

namespace TCSlib.Cryptography.Games.Bridge

open Finset ProbComp

variable {α β ρ σ τ γ : Type}

/-- **Sampling and `uprob` agree:** the probability that a uniform sample of the nonempty finite
type `α` satisfies `p` is `uprob p`.

**Proof sketch.** Both are the number of elements satisfying `p` divided by `|α|`: the sample's
probability is the uniform average of the indicator (`expect_sample`), and `uprob` is the
filter's cardinality over `|α|` (`uprob_eq_card_filter`). -/
theorem prob_sample_eq_uprob [Fintype α] [Nonempty α] (p : α → Prop) :
    prob (sample α) p = uprob p := by
  classical
  rw [prob_eq_expect, expect_sample, uprob_eq_card_filter, sum_boole, inv_mul_eq_div]

/-- **Sampling a pair in sequence is sampling the product:** for every function `g` on pairs,
its expectation over `a ← $ α; b ← $ β; (a, b)` equals its expectation over a uniform pair. -/
theorem expect_sample_pair [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (g : α × β → ℝ) :
    expect ((sample α).bind fun a => (sample β).bind fun b => .pure (a, b)) g =
      expect (sample (α × β)) g := by
  rw [expect_bind, expect_sample, expect_sample, Fintype.card_prod, Fintype.sum_prod_type]
  simp only [expect_bind, expect_sample, expect_pure, Nat.cast_mul, mul_inv, mul_sum]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  ring

/-- Sampling a pair in sequence is sampling the product, for probabilities. -/
theorem prob_sample_pair [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (p : α × β → Prop) :
    prob ((sample α).bind fun a => (sample β).bind fun b => .pure (a, b)) p =
      prob (sample (α × β)) p := by
  classical
  rw [prob_eq_expect, prob_eq_expect, expect_sample_pair]

/-- **Inversion as a game:** `invProb f A` is the probability that the game "sample `x` and the
adversary's coins `r`; win if `A (f x) r` is a preimage of `f x`" is won. [Gar26, Def 2.1] -/
theorem invProb_eq [Fintype α] [Nonempty α] [Fintype ρ] [Nonempty ρ] (f : α → β)
    (A : β → ρ → α) :
    invProb f A =
      prob ((sample α).bind fun x => (sample ρ).bind fun r => .pure (x, r))
        (fun z => f (A (f z.1) z.2) = f z.1) := by
  rw [invProb_def, prob_sample_pair, prob_sample_eq_uprob]

/-- **Prediction as a game:** `predProb f B A` is the probability that `A`, given `f x` and its
coins, outputs `B x`. [Gar26, Def 2.3] -/
theorem predProb_eq [Fintype α] [Nonempty α] [Fintype ρ] [Nonempty ρ] (f : α → β)
    (B : α → Bool) (A : β → ρ → Bool) :
    predProb f B A =
      prob ((sample α).bind fun x => (sample ρ).bind fun r => .pure (x, r))
        (fun z => A (f z.1) z.2 = B z.1) := by
  rw [predProb_def, prob_sample_pair, prob_sample_eq_uprob]

/-- The acceptance game of a sampler `X` and a distinguisher `D`: sample the seed and the coins,
and output `D`'s verdict on the sample. -/
noncomputable def acceptGame [Fintype σ] [Nonempty σ] [Fintype ρ] [Nonempty ρ] (X : σ → γ)
    (D : γ → ρ → Bool) : ProbComp Bool :=
  (sample σ).bind fun s => (sample ρ).bind fun r => .pure (D (X s) r)

/-- The acceptance game samples the seed `s`, then the coins `r`, and outputs `D (X s) r`:
`acceptGame X D = (sample σ).bind fun s => (sample ρ).bind fun r => .pure (D (X s) r)`. -/
theorem acceptGame_eq [Fintype σ] [Nonempty σ] [Fintype ρ] [Nonempty ρ] (X : σ → γ)
    (D : γ → ρ → Bool) :
    acceptGame X D = (sample σ).bind fun s => (sample ρ).bind fun r => .pure (D (X s) r) :=
  rfl

/-- **Acceptance as a game:** `acceptProb X D` is the acceptance probability of `acceptGame X D`.
[Gar26, Defs 3.2 and 3.4] -/
theorem acceptProb_eq [Fintype σ] [Nonempty σ] [Fintype ρ] [Nonempty ρ] (X : σ → γ)
    (D : γ → ρ → Bool) : acceptProb X D = accept (acceptGame X D) := by
  have h : acceptGame X D =
      (fun z : σ × ρ => D (X z.1) z.2) <$>
        ((sample σ).bind fun s => (sample ρ).bind fun r => .pure (s, r)) := by
    simp only [acceptGame_eq, OracleComp.map_eq_bind, OracleComp.bind_assoc, OracleComp.pure_bind]
  rw [acceptProb_def, accept_eq, h, prob_eq_expect, expect_map, ← prob_eq_expect
    (p := fun z : σ × ρ => D (X z.1) z.2 = true), prob_sample_pair, prob_sample_eq_uprob]

/-- **Distinguishing as a game:** `distAdv X Y D` is the advantage between the acceptance games
of `X` and of `Y`. [Gar26, Defs 3.2 and 3.4] -/
theorem distAdv_eq [Fintype σ] [Nonempty σ] [Fintype τ] [Nonempty τ] [Fintype ρ] [Nonempty ρ]
    (X : σ → γ) (Y : τ → γ) (D : γ → ρ → Bool) :
    distAdv X Y D = advantage (acceptGame X D) (acceptGame Y D) := by
  rw [distAdv_def, advantage_eq, acceptProb_eq, acceptProb_eq]

end TCSlib.Cryptography.Games.Bridge

## ===== TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Games
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Handler
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Reduction
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Transfer
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Lazy
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Collision
import Mathlib.Tactic.Simps.Basic
import TCSlib.Cryptography.Foundations.BitLists

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The §3.9 scheme under chosen-plaintext and chosen-ciphertext attacks

[PS10, Theorem 168.2]: the scheme of Algorithm 99.1 (the ch. 2–4 layer's `prfScheme`:
`Enc_k(m) = ⟨r, m ⊕ f_k(r)⟩` for a fresh uniform `r`) is CPA- and CCA1-secure when `F` is a PRF.
[PS10, §7.1.3, Claim 169.a in the inventory]: it is not CCA2-secure, whatever `F`.

The CCA1 statement relies on `Dec` refusing malformed ciphertexts (`prfDecWF`): the evaluator `E`
agrees with `F` only on `⟨s, x⟩` with `|s| = |x|`, and a decryption query must not reach it
elsewhere.

## Main definitions

* `Composability.prfFixedScheme`: `prfScheme`, whose ciphertexts have `3n + 2` bits.

## Main results

* `Composability.prfFixedScheme_cpa`, `Composability.prfFixedScheme_cca1` (Thm 168.2, proved): the
  advantage is at most `prfAdv(F_n, D₀) + prfAdv(F_n, D₁) + (q(n)² + 1) / 2ⁿ`.
* `Composability.prfFixedScheme_not_cca2` (Claim 169.a, proved): an explicit adversary with
  advantage `1`.
* `Composability.not_prfFixedScheme_cca2`: hence the scheme is not CCA2-secure (proved from the
  claim).

## Contents

The proof of Thm 168.2 uses the helper modules under `OracleFromPRF/`:

* `OracleFromPRF.Games`: the IND experiment with a pad function (`PRFGame.fImpl`), and with
  nonce tapes in advance (`eImpl`).
* `OracleFromPRF.Handler`: the reduction's T2 handler (`PRFGame.pkHandler`).
* `OracleFromPRF.Reduction`: the PRF reduction (`PRFGame.exists_prfReduction`).
* `OracleFromPRF.Transfer`: the scheme's oracles as the pad-function experiment.
* `OracleFromPRF.Lazy`: the lazily sampled random function (`PRFGame.expect_lazyImpl`).
* `OracleFromPRF.Collision`: identical until bad and the bad event's bound
  (`PRFGame.abs_expect_fImpl_sub_le`).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Algorithm 99.1, Theorem 168.2 and §7.1.3 (book pp. 99, 168–169; the theorem calls the algorithm
  "construction 99.1").
-/

namespace TCSlib.Cryptography.Composability

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

variable (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
  (E : List Bool → List Bool) (hE : PolyTimeComputable E)
  (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (F n s x))

/-- **The §3.9 scheme with fixed-length ciphertexts**: `⟨r, m ⊕ f_k(r)⟩` with `r` and `m` of `n`
bits has `2n + 2 + n = 3n + 2` bits. -/
noncomputable def prfFixedScheme : FixedLengthScheme where
  toPrivateKeyScheme := prfScheme F E hE hFE
  ctLen := .add (.mul (.const 3) .var) (.const 2)
  enc_length := by
    simp only [prfScheme_gen, prfScheme_enc]
    intro n rg m r
    have hlen : ∀ {f : List Bool → List Bool} (hf : PolyTimeComputable f),
        (NUPPT.ofPolyTimeUniform hf .var).coinLen n = n :=
      fun {f} hf => (NUPPT.coinLen_eq (NUPPT.ofPolyTimeUniform hf .var) n).trans
        ((congrArg (fun p : PolyExpr => p.eval n)
          (NUPPT.coins_ofPolyTimeUniform hf .var)).trans (PolyExpr.eval_var n))
    let k : Fin n → Bool := fun j =>
      rg (Fin.cast (hlen polyTimeComputable_pairSndD).symm j)
    let x : Fin n → Bool := fun j =>
      r (Fin.cast (hlen (polyTimeComputable_prfEncFun hE)).symm j)
    have hk : List.ofFn rg = List.ofFn k :=
      List.ofFn_congr (hlen polyTimeComputable_pairSndD) rg
    have hx : List.ofFn r = List.ofFn x :=
      List.ofFn_congr (hlen (polyTimeComputable_prfEncFun hE)) r
    rw [runAt_coinKey, runAt_prfEnc hE, hk, hx, hFE, length_pairEncode]
    simp only [List.length_zipWith, List.length_ofFn, Nat.min_self, PolyExpr.eval_add,
      PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    omega

attribute [simps (config := { isSimp := false }) toPrivateKeyScheme ctLen] prfFixedScheme

/-- The fixed-length scheme uses the key generator of `prfScheme`. -/
theorem prfFixedScheme_gen :
    (prfFixedScheme F E hE hFE).gen = (prfScheme F E hE hFE).gen :=
  congrArg PrivateKeyScheme.gen (prfFixedScheme_toPrivateKeyScheme F E hE hFE)

/-- The fixed-length scheme uses the encryption machine of `prfScheme`. -/
theorem prfFixedScheme_enc :
    (prfFixedScheme F E hE hFE).enc = (prfScheme F E hE hFE).enc :=
  congrArg PrivateKeyScheme.enc (prfFixedScheme_toPrivateKeyScheme F E hE hFE)

/-- The fixed-length scheme uses the decryption machine of `prfScheme`. -/
theorem prfFixedScheme_dec :
    (prfFixedScheme F E hE hFE).dec = (prfScheme F E hE hFE).dec :=
  congrArg PrivateKeyScheme.dec (prfFixedScheme_toPrivateKeyScheme F E hE hFE)

/-! ### Step 1: the game is the experiment with pad function `f_k` -/

section PRFStep

open PRFGame ChallengeSim ProbComp

/-- **The key generator outputs its coins:** `Gen(1^n; rg) = ⟦rg⟧` (`runAt_coinKey`). -/
private theorem prf_gen_runAt (n : ℕ) :
    ∀ rg : (prfFixedScheme F E hE hFE).gen.Coins n,
      (prfFixedScheme F E hE hFE).gen.runAt n [] rg = List.ofFn rg := by
  rw [prfFixedScheme_gen, prfScheme_gen]
  intro rg
  exact runAt_coinKey .var n rg

/-- The key coins as an `n`-bit key, keeping the string. -/
private noncomputable def prfKeyEq (n : ℕ) :
    (prfFixedScheme F E hE hFE).gen.Coins n ≃ (Fin n → Bool) :=
  (NUPPT.coinsCongr (by rw [prfFixedScheme_gen, prfScheme_gen]) n).trans
    ((NUPPT.coinsEquiv_ofPolyTimeUniform polyTimeComputable_pairSndD .var n).trans
      (Equiv.arrowCongr (finCongr (PolyExpr.eval_var n)) (Equiv.refl Bool)))

/-- `⟦prfKeyEq n rg⟧ = ⟦rg⟧`. -/
private theorem ofFn_prfKeyEq (n : ℕ) (rg : (prfFixedScheme F E hE hFE).gen.Coins n) :
    List.ofFn (prfKeyEq F E hE hFE n rg) = List.ofFn rg := by
  rw [prfKeyEq, Equiv.trans_apply, Equiv.trans_apply, ofFn_arrowCongr_finCongr,
    NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn, NUPPT.coinsCongr_ofFn]

/-- The encryption coins as an `n`-bit nonce, keeping the string. -/
private noncomputable def prfNonceEq (n : ℕ) :
    (prfFixedScheme F E hE hFE).enc.Coins n ≃ (Fin n → Bool) :=
  (NUPPT.coinsCongr (by rw [prfFixedScheme_enc, prfScheme_enc]) n).trans
    ((NUPPT.coinsEquiv_ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) .var n).trans
      (Equiv.arrowCongr (finCongr (PolyExpr.eval_var n)) (Equiv.refl Bool)))

/-- `⟦prfNonceEq n re⟧ = ⟦re⟧`. -/
private theorem ofFn_prfNonceEq (n : ℕ) (re : (prfFixedScheme F E hE hFE).enc.Coins n) :
    List.ofFn (prfNonceEq F E hE hFE n re) = List.ofFn re := by
  rw [prfNonceEq, Equiv.trans_apply, Equiv.trans_apply, ofFn_arrowCongr_finCongr,
    NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn, NUPPT.coinsCongr_ofFn]

/-- **Encryption with the key `k` and the coins `re`** is the ciphertext `⟨r, m ⊕ F_k(r)⟩` with the
nonce `r = prfNonceEq re` (`runAt_prfEnc`, `hFE`). -/
private theorem ofFn_prf_encryptAt (n : ℕ) (k m : Fin n → Bool)
    (re : (prfFixedScheme F E hE hFE).enc.Coins n) :
    List.ofFn ((prfFixedScheme F E hE hFE).encryptAt n (List.ofFn k) m re) =
      ctOf (prfNonceEq F E hE hFE n re) (List.ofFn m)
        (F n k (prfNonceEq F E hE hFE n re)) := by
  have hx : List.ofFn re = List.ofFn (prfNonceEq F E hE hFE n re) :=
    (ofFn_prfNonceEq F E hE hFE n re).symm
  generalize prfNonceEq F E hE hFE n re = x at hx
  revert re
  simp only [FixedLengthScheme.encryptAt_eq, prfFixedScheme_ctLen]
  rw [prfFixedScheme_enc, prfScheme_enc]
  intro re hx
  rw [runAt_prfEnc hE, hx, hFE, ctOf_eq]
  apply ofFn_padFin_of_length
  simp only [length_pairEncode, List.length_ofFn, List.length_zipWith, Nat.min_self,
    PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  omega

/-- **Decryption with the key `k`**, for `n > 0`: on a well-formed `w = ⟨x, v⟩` the answer is
`⟨1, v ⊕ F_k(x)⟩`, and otherwise `⊥` (`runAt_prfDec`, `decodeFin_runAt_prfDec_of_not_wf`). -/
private theorem ofFn_prf_decAnswer (n : ℕ) (hn : 0 < n) (k : Fin n → Bool) (w : List Bool)
    (rd : (prfFixedScheme F E hE hFE).dec.Coins n) :
    List.ofFn (FixedLengthScheme.decAnswer (decodeFin n
        ((prfFixedScheme F E hE hFE).dec.runAt n (pairEncode (List.ofFn k) w) rd))) =
      if decWF n w then
        true :: List.zipWith xor (pairSndD w) (List.ofFn (F n k (padFin n (pairFstD w))))
      else List.replicate (n + 1) false := by
  revert rd
  rw [prfFixedScheme_dec, prfScheme_dec]
  intro rd
  by_cases hw : decWF n w = true
  · rw [if_pos hw]
    rw [decWF_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hw
    have hne : pairFstD w ≠ [] := by
      intro h
      have := hw.1
      rw [h, List.length_nil] at this
      omega
    have hx : pairFstD w = List.ofFn (padFin n (pairFstD w)) :=
      (ofFn_padFin_of_length hw.1).symm
    have hv : List.zipWith xor (pairSndD w) (List.ofFn (F n k (padFin n (pairFstD w)))) =
        List.ofFn (padFin n (List.zipWith xor (pairSndD w)
          (List.ofFn (F n k (padFin n (pairFstD w)))))) :=
      (ofFn_padFin_of_length (by
        rw [List.length_zipWith, List.length_ofFn, hw.2, Nat.min_self])).symm
    conv_lhs => rw [eq_pairEncode_of_pairFstD_ne hne]
    rw [runAt_prfDec hE _ n _ _ _ hw.1 hw.2, hx, hFE, ← hx, hv, decodeFin_ofFn,
      FixedLengthScheme.decAnswer_some, List.ofFn_succ, Fin.cons_zero]
    simp only [Fin.cons_succ]
  · rw [if_neg hw, decodeFin_runAt_prfDec_of_not_wf hE _ n _ w (by
      rw [decWF_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hw
      exact hw), FixedLengthScheme.decAnswer_none, ofFn_zeroBits]

/-- The scheme's ciphertexts have `ctP(n) = 3n + 2` bits. -/
private theorem prf_ctLen_eval (n : ℕ) :
    (prfFixedScheme F E hE hFE).ctLen.eval n = ctP.eval n := by
  rw [prfFixedScheme_ctLen, ctP_eval, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
    PolyExpr.eval_const, PolyExpr.eval_var]

/-- The scheme's query lengths are the reduction's: `inLens n = fun i => (pkDin i).eval n`. -/
private theorem prf_inLens (n : ℕ) :
    (prfFixedScheme F E hE hFE).inLens n = fun i => (pkDin i).eval n := by
  funext i
  match i with
  | 0 => rw [FixedLengthScheme.inLens_zero, pkDin_zero, PolyExpr.eval_var]
  | 1 => rw [FixedLengthScheme.inLens_one, pkDin_one, prf_ctLen_eval]
  | 2 => rw [FixedLengthScheme.inLens_two, pkDin_two, PolyExpr.eval_add, PolyExpr.eval_var]

/-- The scheme's answer lengths are the reduction's: `outLens n = fun i => (pkDout i).eval n`. -/
private theorem prf_outLens (n : ℕ) :
    (prfFixedScheme F E hE hFE).outLens n = fun i => (pkDout i).eval n := by
  funext i
  match i with
  | 0 => rw [FixedLengthScheme.outLens_zero, pkDout_zero, prf_ctLen_eval]
  | 1 =>
    rw [FixedLengthScheme.outLens_one, pkDout_one, PolyExpr.eval_add, PolyExpr.eval_var,
      PolyExpr.eval_const]
  | 2 => rw [FixedLengthScheme.outLens_two, pkDout_two, prf_ctLen_eval]

/-- **The IND experiment of the scheme is the experiment with pad function `F_k`** (step 1,
`n > 0`, CPA or CCA1): `Pr[IND_b = 1] = 𝔼_k 𝔼_r Pr[A outputs 1 against fImpl … (F n k)]`, on the
reduction's lengths.

**Proof sketch.** The key generator outputs its uniform coins (`prf_gen_runAt`, `prfKeyEq`); for
every key, the oracles of `IND_b` and `fImpl … (F n k)` have the same laws call by call
(`expect_indImpl_fImpl`, from `ofFn_prf_encryptAt` and `ofFn_prf_decAnswer`), so the simulations
agree (`ProbComp.expect_simulate_congr`); the game's codec and lengths are the reduction's
(`FixedLengthScheme.indCodec_eq_bitCodec`, `prf_inLens`, `prf_outLens`, `prf_ctLen_eval`). -/
private theorem accept_prf_indGame (atkBit b : Bool) (A : NUPPT) (Q n : ℕ) (hn : 0 < n) :
    accept ((prfFixedScheme F E hE hFE).indGame (atkOf atkBit) A Q b n) =
      expect (ProbComp.sample (Fin n → Bool)) fun k =>
        expect (ProbComp.sample (A.Coins n)) fun r =>
          expect (simulate (fImpl (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
              (ctP.eval n) n (atkOf atkBit) b (F n k))
              (A.toComp (bitCodec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n) 1) n Q r)
              none)
            (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
  have hct : (prfFixedScheme F E hE hFE).ctLen.eval n = 3 * n + 2 := by
    rw [prf_ctLen_eval, ctP_eval]
  rw [accept_eq, FixedLengthScheme.indGame_eq, prob_bind,
    ← expect_sample_equiv (prfKeyEq F E hE hFE n)]
  refine congrArg _ (funext fun rg => ?_)
  have hk : (prfFixedScheme F E hE hFE).gen.runAt n [] rg =
      List.ofFn (prfKeyEq F E hE hFE n rg) := by
    rw [prf_gen_runAt, ofFn_prfKeyEq]
  rw [hk, prob_bind]
  refine congrArg _ (funext fun r => ?_)
  rw [prob_bind]
  have h1 : (fun res : (Fin 1 → Bool) × Option (Fin ((prfFixedScheme F E hE hFE).ctLen.eval n) →
      Bool) => ProbComp.prob (.pure (res.1 0)) (· = true)) =
      fun res => if (List.ofFn res.1).headD false = true then (1 : ℝ) else 0 := by
    funext res
    rw [prob_pure, headD_ofFn_one]
  rw [h1, expect_simulate_congr _ _ (fun i x s g => expect_indImpl_fImpl _ atkBit b n _ _ hct
      (prfNonceEq F E hE hFE n) (fun m re => ofFn_prf_encryptAt F E hE hFE n _ m re)
      (fun w rd => ofFn_prf_decAnswer F E hE hFE n hn _ w rd) i x s g),
    FixedLengthScheme.indCodec_eq_bitCodec]
  exact expect_fImpl_transport (prf_inLens F E hE hFE n) (prf_outLens F E hE hFE n)
    (prf_ctLen_eval F E hE hFE n) n _ b _ A Q r

/-- **The reduction's PRF advantage is the gap between the experiments with `F_k` and with a
random function** (step 1): for the machine `D` of `exists_prfReduction` and `n > 0`,
`prfAdv (F n) D = |Pr[IND_b = 1] − 𝔼_R 𝔼_r Pr[A outputs 1 against fImpl … R]|`.

**Proof sketch.** `prfAdv_def`, `distAdv_def`; each acceptance probability is an average over the
key (resp. the function table) and `D`'s coins (`Bridge.acceptProb_eq`, `acceptGame_eq`,
`oracleDist_apply`, `randomFunction_apply`), which `D`'s defining property turns into the
experiment with that function; with the key it is the game (`accept_prf_indGame`). -/
private theorem prfAdv_prfReduction (atkBit b : Bool) (A : NUPPT) (q : PolyExpr) (D : NUPPT)
    (hD : ∀ (n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool)),
      expect (ProbComp.sample (D.Coins n))
          (fun c => if (D.toOracleAdversary n n n ((qRed q).eval n) c).eval f = true
            then (1 : ℝ) else 0) =
        expect (ProbComp.sample (A.Coins n)) fun r =>
          expect (simulate (fImpl (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
              (ctP.eval n) n (atkOf atkBit) b f)
              (A.toComp (bitCodec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n) 1) n
                (q.eval n) r) none)
            (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0))
    (n : ℕ) (hn : 0 < n) :
    prfAdv (F n) (D.toOracleAdversary n n n ((qRed q).eval n)) =
      |accept ((prfFixedScheme F E hE hFE).indGame (atkOf atkBit) A (q.eval n) b n) -
        expect (ProbComp.sample ((Fin n → Bool) → (Fin n → Bool))) fun R =>
          expect (ProbComp.sample (A.Coins n)) fun r =>
            expect (simulate (fImpl (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
                (ctP.eval n) n (atkOf atkBit) b R)
                (A.toComp (bitCodec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n) 1) n
                  (q.eval n) r) none)
              (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0)| := by
  rw [prfAdv_def, distAdv_def, accept_prf_indGame F E hE hFE atkBit b A _ n hn,
    Bridge.acceptProb_eq, Bridge.acceptProb_eq, accept_eq, accept_eq, Bridge.acceptGame_eq,
    Bridge.acceptGame_eq, prob_bind, prob_bind]
  congr 2
  · refine congrArg _ (funext fun k => ?_)
    simp only [prob_bind, prob_pure, oracleDist_apply]
    exact hD n (F n k)
  · refine congrArg _ (funext fun R => ?_)
    simp only [prob_bind, prob_pure, oracleDist_apply, randomFunction_apply]
    exact hD n R

/-- **The bound at each security parameter** (steps 1–3 of [PS10, Thm 168.2]): for CPA or CCA1
there are PRF distinguishers `D₀`, `D₁` (one per bit) with
`adv_n ≤ prfAdv(F_n, D₀) + prfAdv(F_n, D₁) + (q(n)² + 1) / 2ⁿ`.

**Proof sketch.** `D_b` is `exists_prfReduction` for the bit `b`. For `n > 0`, the triangle
inequality through the experiments with a uniform random function: each game is within
`prfAdv(F_n, D_b)` of its random-function experiment (`prfAdv_prfReduction`), and the two
random-function experiments are within `q(n)² / 2ⁿ` (`PRFGame.abs_expect_fImpl_sub_le`; the
adversary makes at most `q(n)` queries, `NUPPT.toComp_costBoundedBy`). For `n = 0`, `adv ≤ 1`. -/
private theorem prf_advantage_le (atkBit : Bool) (A : NUPPT) (q : PolyExpr) :
    ∃ D₀ D₁ : NUPPT, ∀ n,
      advantage ((prfFixedScheme F E hE hFE).indGame (atkOf atkBit) A (q.eval n) false n)
          ((prfFixedScheme F E hE hFE).indGame (atkOf atkBit) A (q.eval n) true n) ≤
        prfAdv (F n) (D₀.toOracleAdversary n n n ((qRed q).eval n)) +
          prfAdv (F n) (D₁.toOracleAdversary n n n ((qRed q).eval n)) +
          ((((q.mul q).add (.const 1)).eval n : ℕ) : ℝ) * (2⁻¹ : ℝ) ^ n := by
  obtain ⟨D₀, hD₀⟩ := exists_prfReduction A q atkBit false
  obtain ⟨D₁, hD₁⟩ := exists_prfReduction A q atkBit true
  refine ⟨D₀, D₁, fun n => ?_⟩
  have hp : ∀ D : NUPPT, 0 ≤ prfAdv (F n) (D.toOracleAdversary n n n ((qRed q).eval n)) :=
    fun D => by rw [prfAdv_def, distAdv_def]; exact abs_nonneg _
  have hQ : ((((q.mul q).add (.const 1)).eval n : ℕ) : ℝ) * (2⁻¹ : ℝ) ^ n =
      ((q.eval n : ℝ) ^ 2 + 1) / 2 ^ n := by
    rw [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, inv_pow]
    push_cast
    ring
  have hQ1 : ((q.eval n : ℝ) ^ 2) / 2 ^ n ≤ ((q.eval n : ℝ) ^ 2 + 1) / 2 ^ n :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  rw [hQ]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : (1 : ℝ) ≤ ((q.eval 0 : ℝ) ^ 2 + 1) / 2 ^ 0 := by
      rw [pow_zero, div_one]
      nlinarith [sq_nonneg (q.eval 0 : ℝ)]
    linarith [advantage_le_one ((prfFixedScheme F E hE hFE).indGame (atkOf atkBit) A (q.eval 0)
      false 0) ((prfFixedScheme F E hE hFE).indGame (atkOf atkBit) A (q.eval 0) true 0), hp D₀,
      hp D₁]
  · have key : ∀ a₀ a₁ X₀ X₁ K : ℝ, |X₀ - X₁| ≤ K → |a₀ - a₁| ≤ |a₀ - X₀| + |a₁ - X₁| + K :=
      fun a₀ a₁ X₀ X₁ K h => by
        have t1 := abs_sub_le a₀ X₀ a₁
        have t2 := abs_sub_le X₀ X₁ a₁
        rw [abs_sub_comm X₁ a₁] at t2
        linarith
    rw [advantage_eq, prfAdv_prfReduction F E hE hFE atkBit false A q D₀ hD₀ n hn,
      prfAdv_prfReduction F E hE hFE atkBit true A q D₁ hD₁ n hn]
    refine key _ _ _ _ _ (le_trans ?_ hQ1)
    exact abs_expect_fImpl_sub_le (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
      (ctP.eval n) n (atkOf atkBit) (by rw [decOpen_atkOf, Bool.not_true, Bool.and_false])
      (ctP_eval n)
      (by show (pkDin 2).eval n = n + n; rw [pkDin_two, PolyExpr.eval_add, PolyExpr.eval_var])
      (fun r => A.toComp (bitCodec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n) 1) n
        (q.eval n) r) (fun a => (List.ofFn a).headD false = true) (q.eval n)
      (fun r => A.toComp_costBoundedBy _ n _ r)

/-- **Theorem 168.2 for CPA (`atkBit = false`) and CCA1 (`atkBit = true`).**

**Proof sketch.** `prf_advantage_le` bounds the advantage by
`prfAdv(F_n, D₀) + prfAdv(F_n, D₁) + (q(n)² + 1) · 2⁻ⁿ`, which is negligible: both PRF advantages
are (`PRF.negligible_prfAdv`, budget `qRed q`), and so is a polynomial times `2⁻ⁿ`
(`EnsembleLemmas.negligible_polyExpr_mul`, `negligible_two_pow_neg`); sums of negligible functions
are negligible (`Negligible.add`). -/
private theorem prf_indSecure (atkBit : Bool) (hF : PRF F) :
    (prfFixedScheme F E hE hFE).INDSecure (atkOf atkBit) := by
  rw [FixedLengthScheme.INDSecure_iff]
  intro A q
  obtain ⟨D₀, D₁, h⟩ := prf_advantage_le F E hE hFE atkBit A q
  exact ⟨_, ((hF.negligible_prfAdv D₀ (qRed q)).add (hF.negligible_prfAdv D₁ (qRed q))).add
    (EnsembleLemmas.negligible_polyExpr_mul _ negligible_two_pow_neg), h⟩

end PRFStep

/-- **Theorem 168.2 (CPA)** [PS10]: if `F` is a pseudorandom function family, the §3.9 scheme is
CPA-secure.

**Deviation:** [PS10]'s proof is qualitative (a PRF reduction and a negligible collision event);
the issued brief suggested the bound `2 · prfAdv + q(n)/2ⁿ` with one reduction carrying the
challenge bit in its seed. Here there is one reduction per bit (the bit hard-wired) and the bound is
`prfAdv(F_n, D₀) + prfAdv(F_n, D₁) + (q(n)² + 1) / 2ⁿ`: the bad event is bounded query by query
(at most `q` steps, each against at most `q` points), and the `+ 1` covers `n = 0`.

**Proof sketch.**
1. *PRF → random function* (`PRFGame.exists_prfReduction`, `prfAdv_prfReduction`): for each bit
   `b`, a reduction `D_b` built with T2 (`Games.exists_interactiveHandlerMachine`, the handler
   `PRFGame.pkHandler`), the input-free companion and T4
   (`Games.exists_toOracleAdversary_of_bitCodec`) answers `Enc` and the challenge by querying its
   function oracle at a fresh `r`. With `f_k` it accepts exactly when the IND experiment does;
   with a random function `R`, exactly when the experiment with pad `R` does. So each game is within
   `prfAdv(F_n, D_b)` of its random-function experiment.
2. *The random-function experiment* (`PRFGame.abs_expect_fImpl_sub_le`): sample `R` lazily
   (`PRFGame.expect_lazyImpl`). The bad event is that the challenge's `r*` was already asked or
   a later `Enc` uses it; a query raises it with probability at most `(q + 1) / 2ⁿ` (`prob_mem_le`),
   so it has probability at most `q(n)² / 2ⁿ` (`ProbComp.prob_bad_le`). Off the bad event,
   `m_b ⊕ R(r*)` is uniform for both `b` (identical until bad, `identical_until_bad`, with the pad
   changed by `y ↦ y ⊕ m₀ ⊕ m₁`).
3. *The bound* (`prf_advantage_le`, `prf_indSecure`): the triangle inequality gives the bound
   above (`advantage ≤ 1` at `n = 0`); it is negligible (`PRF.negligible_prfAdv`,
   `EnsembleLemmas.negligible_polyExpr_mul`, `negligible_two_pow_neg`). -/
theorem prfFixedScheme_cpa (hF : PRF F) : (prfFixedScheme F E hE hFE).INDSecure .cpa := by
  rw [← PRFGame.atkOf_false]
  exact prf_indSecure F E hE hFE false hF

/-- **Theorem 168.2 (CCA1)** [PS10]: if `F` is a pseudorandom function family, the §3.9 scheme
is CCA1-secure.

**Deviation:** as for CPA, one reduction per bit and the bound
`prfAdv(F_n, D₀) + prfAdv(F_n, D₁) + (q(n)² + 1) / 2ⁿ`.

**Proof sketch.** As for CPA, with the reduction also answering decryption queries before the
challenge with its oracle (`Dec_k(⟨r, c⟩) = c ⊕ f_k(r)` on well-formed ciphertexts,
`PRFGame.pkHandler_impl_dec_open`; `⊥` on the others, `pkHandler_impl_dec_closed`; the scheme's
answers are matched by `runAt_prfDec` and `decodeFin_runAt_prfDec_of_not_wf`). In the lazy
experiment a pre-challenge decryption enters its nonce in the table, so the bad event adds the case
that it is the challenge's `r*`, again bounded by `prob_mem_le` because `r*` is drawn after those
queries; after the challenge CCA1 refuses decryption, so it never reads `b`. -/
theorem prfFixedScheme_cca1 (hF : PRF F) : (prfFixedScheme F E hE hFE).INDSecure .cca1 := by
  rw [← PRFGame.atkOf_true]
  exact prf_indSecure F E hE hFE true hF

/-- Reverse the word, negate its first bit, and reverse back: on a nonempty word this
flips exactly its last bit. -/
private def cca2FlipLast (w : List Bool) : List Bool :=
  ([!w.reverse.headD false] ++ w.reverse.drop 1).reverse

/-- Flipping the last bit is polynomial-time by reversal, head, tail and negation. -/
private theorem cca2FlipLast_poly : PolyTimeComputable cca2FlipLast := by
  exact (BinArith.polyTimeComputable_reverse.comp
    ((polyTimeComputable_not (polyTimeComputable_headD.comp
      BinArith.polyTimeComputable_reverse)).append
        (polyTimeComputable_tail.comp BinArith.polyTimeComputable_reverse)))

/-- On a word ending in `b`, the flip replaces that bit by `!b`. -/
private theorem cca2FlipLast_snoc (w : List Bool) (b : Bool) :
    cca2FlipLast (w ++ [b]) = w ++ [!b] := by
  simp only [cca2FlipLast, List.reverse_append, List.reverse_nil, List.nil_append,
    List.singleton_append, List.headD_cons, List.drop_succ_cons, List.drop_zero,
    List.reverse_cons, List.reverse_reverse]

/-- A nonempty suffix contains the last bit, so a prefix is unchanged by the flip. -/
private theorem cca2FlipLast_append (u v : List Bool) (hv : v ≠ []) :
    cca2FlipLast (u ++ v) = u ++ cca2FlipLast v := by
  rcases List.eq_nil_or_concat' v with h | ⟨v, b, rfl⟩
  · exact (hv h).elim
  · simp only [← List.append_assoc, cca2FlipLast_snoc]

/-- Flipping a nonempty ciphertext payload preserves the nonce and pairing delimiter. -/
private theorem cca2FlipLast_pair (u v : List Bool) (hv : v ≠ []) :
    cca2FlipLast (pairEncode u v) = pairEncode u (cca2FlipLast v) := by
  rw [pairEncode_eq, pairEncode_eq, cca2FlipLast_append _ v hv]

/-- The modified word has its original length whenever that word is nonempty. -/
private theorem cca2FlipLast_length (w : List Bool) (hw : w ≠ []) :
    (cca2FlipLast w).length = w.length := by
  rcases List.eq_nil_or_concat' w with h | ⟨w, b, rfl⟩
  · exact (hw h).elim
  · simp only [cca2FlipLast_snoc, List.length_append, List.length_singleton]

/-- The flipped word differs from the original at its last bit. -/
private theorem cca2FlipLast_ne (w : List Bool) (hw : w ≠ []) :
    cca2FlipLast w ≠ w := by
  rcases List.eq_nil_or_concat' w with h | ⟨w, b, rfl⟩
  · exact (hw h).elim
  · rw [cca2FlipLast_snoc]
    intro he
    have hb := congrArg (fun v : List Bool => v.getLastD false) he
    simp only [List.getLastD_concat] at hb
    cases b <;> cases hb

/-- Negate precisely the bit whose index is one less than the vector length. -/
private def cca2FlipBits {n : ℕ} (m : Fin n → Bool) : Fin n → Bool :=
  fun i => if i.val + 1 = n then !m i else m i

/-- The list and vector versions of the last-bit flip agree at positive lengths. -/
private theorem cca2FlipLast_ofFn {n : ℕ} (hn : 0 < n) (m : Fin n → Bool) :
    cca2FlipLast (List.ofFn m) = List.ofFn (cca2FlipBits m) := by
  cases n with
  | zero => omega
  | succ n =>
    rw [List.ofFn_succ_last, cca2FlipLast_snoc, List.ofFn_succ_last]
    congr 1
    · apply congrArg List.ofFn
      funext i
      have hi : i.val + 1 ≠ n + 1 := by omega
      change m i.castSucc = if i.val + 1 = n + 1 then !m i.castSucc else m i.castSucc
      rw [if_neg hi]
    · change [!m (Fin.last n)] =
        [if n + 1 = n + 1 then !m (Fin.last n) else m (Fin.last n)]
      rw [if_pos rfl]

/-- Flipping one bit commutes with removing an exclusive-or pad. -/
private theorem cca2FlipBits_unmask {n : ℕ} (m p : Fin n → Bool) :
    cca2FlipBits (m + p) + p = cca2FlipBits m := by
  funext i
  change xor (if i.val + 1 = n then !(xor (m i) (p i)) else xor (m i) (p i)) (p i) =
    if i.val + 1 = n then !m i else m i
  split <;> cases m i <;> cases p i <;> rfl

/-- The attack's next activation asks the challenge, asks decryption of the modified
challenge, or negates the last bit of the second answer, according to the log. -/
private def cca2Next (z : List Bool) : List Bool :=
  let h := NUPPT.inArg z
  if h = [] then
    pairEncode [false] (pairEncode [true, true]
      (List.zipWith xor (NUPPT.inParam z) (NUPPT.inParam z) ++ NUPPT.inParam z))
  else if pairSndD h = [] then
    pairEncode [false] (pairEncode [true]
      (cca2FlipLast (pairSndD (pairSndD (pairFstD h)))))
  else pairEncode [true]
    [!(pairSndD (pairSndD (pairFstD (pairSndD h)))).getLastD false]

/-- The three activations are polynomial-time: projections, emptiness tests, pairing,
exclusive-or, the last-bit flip, and a last-bit test followed by negation. -/
private theorem cca2Next_poly : PolyTimeComputable cca2Next := by
  have ha := NUPPT.polyTimeComputable_inArg
  have hp := NUPPT.polyTimeComputable_inParam
  have ht := polyTimeComputable_pairSndD.comp ha
  have hz : PolyTimeComputable (fun z =>
      List.zipWith xor (NUPPT.inParam z) (NUPPT.inParam z)) :=
    (polyTimeComputable_pairXor.comp (hp.pairEncode hp)).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hans : PolyTimeComputable (fun z => pairSndD (pairSndD (pairFstD z))) :=
    polyTimeComputable_pairSndD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)
  have h := polyTimeComputable_ite (polyTimeComputable_isNil.comp ha)
    ((polyTimeComputable_const [false]).pairEncode
      ((polyTimeComputable_const [true, true]).pairEncode
        (hz.append hp)))
    (polyTimeComputable_ite (polyTimeComputable_isNil.comp ht)
      ((polyTimeComputable_const [false]).pairEncode
        ((polyTimeComputable_const [true]).pairEncode
          (cca2FlipLast_poly.comp (hans.comp ha))))
      ((polyTimeComputable_const [true]).pairEncode
        (polyTimeComputable_not (BinArith.polyTimeComputable_lastBit.comp (hans.comp ht)))))
  exact h.congr fun z => by
    simp only [cca2Next, Function.comp_apply, decide_eq_true_eq]

/-- The uniform deterministic machine implementing the three activations. -/
private noncomputable def cca2Adversary : NUPPT :=
  NUPPT.ofPolyTimeUniform cca2Next_poly (.const 0)

/-- An activation reads only its argument and the unary parameter; its coins are ignored. -/
private theorem cca2Adversary_run (n : ℕ) (h : List Bool) (r : cca2Adversary.Coins n) :
    cca2Adversary.runAt n h r =
      if h = [] then
        pairEncode [false] (pairEncode [true, true]
          (List.replicate n false ++ List.replicate n true))
      else if pairSndD h = [] then
        pairEncode [false] (pairEncode [true]
          (cca2FlipLast (pairSndD (pairSndD (pairFstD h)))))
      else pairEncode [true]
        [!(pairSndD (pairSndD (pairFstD (pairSndD h)))).getLastD false] := by
  unfold cca2Adversary
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform, cca2Next]
  simp only [NUPPT.inArg_eq, NUPPT.inParam_eq, NUPPT.advInput_eq,
    pairFstD_pairEncode, pairSndD_pairEncode, List.zipWith_replicate,
    Nat.min_self, Bool.xor_self]

/-- A one-entry log makes the second activation query the flipped challenge answer. -/
private theorem cca2Adversary_one (n : ℕ) (i x c : List Bool)
    (r : cca2Adversary.Coins n) :
    cca2Adversary.runAt n (pairEncode (pairEncode i (pairEncode x c)) []) r =
      pairEncode [false] (pairEncode [true] (cca2FlipLast c)) := by
  rw [cca2Adversary_run]
  have hn : pairEncode (pairEncode i (pairEncode x c)) [] ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp only [length_pairEncode, List.length_nil] at hh
    omega
  simp only [hn, ite_false, pairFstD_pairEncode, pairSndD_pairEncode, ite_true]

/-- A two-entry log makes the final activation negate the last bit of its second answer. -/
private theorem cca2Adversary_two (n : ℕ) (i x c j y d : List Bool)
    (r : cca2Adversary.Coins n) :
    cca2Adversary.runAt n
      (pairEncode (pairEncode i (pairEncode x c))
        (pairEncode (pairEncode j (pairEncode y d)) [])) r =
      pairEncode [true] [!d.getLastD false] := by
  rw [cca2Adversary_run]
  have hn : ∀ a b : List Bool, pairEncode a b ≠ [] := by
    intro a b he
    have hh := congrArg List.length he
    simp only [length_pairEncode, List.length_nil] at hh
    omega
  simp only [hn, ite_false, pairFstD_pairEncode, pairSndD_pairEncode]

/-- For every encryption tape there is an `n`-bit nonce `x`; the ciphertext is exactly
the pair of that nonce and the message masked by `F n k x` (`ofFn_prf_encryptAt` with the nonce
`prfNonceEq r`). -/
private theorem cca2Encrypt (n : ℕ) (k m : Fin n → Bool)
    (r : (prfFixedScheme F E hE hFE).enc.Coins n) :
    ∃ x : Fin n → Bool, List.ofFn r = List.ofFn x ∧
      List.ofFn ((prfFixedScheme F E hE hFE).encryptAt n (List.ofFn k) m r) =
        pairEncode (List.ofFn x) (List.ofFn (m + F n k x)) := by
  refine ⟨prfNonceEq F E hE hFE n r, (ofFn_prfNonceEq F E hE hFE n r).symm, ?_⟩
  rw [ofFn_prf_encryptAt, PRFGame.ctOf_eq, zipWith_xor_ofFn_add]

/-- The challenge query concatenates the all-false and all-true messages. -/
private def cca2Messages (n : ℕ) : Fin (n + n) → Bool :=
  Fin.append (fun _ => false) (fun _ => true)

/-- The challenge query's word is `0^n ++ 1^n`. -/
private theorem cca2Messages_ofFn (n : ℕ) :
    List.ofFn (cca2Messages n) = List.replicate n false ++ List.replicate n true := by
  rw [cca2Messages, List.ofFn_fin_append, List.ofFn_const, List.ofFn_const]

/-- Selecting challenge half `b` selects the constant message `b`. -/
private theorem cca2Messages_choice (n : ℕ) (b : Bool) :
    (if b then (FixedLengthScheme.splitHalf (cca2Messages n)).2
      else (FixedLengthScheme.splitHalf (cca2Messages n)).1) = fun _ => b := by
  cases b with
  | false =>
    change (FixedLengthScheme.splitHalf (cca2Messages n)).1 = fun _ => false
    rw [FixedLengthScheme.splitHalf_fst]
    funext i
    exact Fin.append_left _ _ i
  | true =>
    change (FixedLengthScheme.splitHalf (cca2Messages n)).2 = fun _ => true
    rw [FixedLengthScheme.splitHalf_snd]
    funext i
    exact Fin.append_right _ _ i

/-- The modified fixed-width ciphertext reads the word with its last bit flipped. -/
private def cca2Alter {d : ℕ} (c : Fin d → Bool) : Fin d → Bool :=
  padFin d (cca2FlipLast (List.ofFn c))

/-- At positive width the modified ciphertext has exactly the flipped word. -/
private theorem cca2Alter_ofFn {d : ℕ} (hd : 0 < d) (c : Fin d → Bool) :
    List.ofFn (cca2Alter c) = cca2FlipLast (List.ofFn c) := by
  apply ofFn_padFin_of_length
  rw [cca2FlipLast_length]
  · exact List.length_ofFn
  · intro he
    have hh := congrArg List.length he
    simp only [List.length_ofFn, List.length_nil] at hh
    omega

/-- At positive width the modified ciphertext differs from the recorded challenge. -/
private theorem cca2Alter_ne {d : ℕ} (hd : 0 < d) (c : Fin d → Bool) :
    cca2Alter c ≠ c := by
  intro he
  have hh := congrArg List.ofFn he
  rw [cca2Alter_ofFn hd] at hh
  apply cca2FlipLast_ne (List.ofFn c) ?_ hh
  intro hc
  have hl := congrArg List.length hc
  simp only [List.length_ofFn, List.length_nil] at hl
  omega

/-- Every generated key is an `n`-bit word (`prf_gen_runAt`, `ofFn_prfKeyEq`). -/
private theorem cca2Gen (n : ℕ) (rg : (prfFixedScheme F E hE hFE).gen.Coins n) :
    ∃ k : Fin n → Bool, (prfFixedScheme F E hE hFE).gen.runAt n [] rg = List.ofFn k :=
  ⟨prfKeyEq F E hE hFE n rg, by rw [prf_gen_runAt, ofFn_prfKeyEq]⟩

/-- The actual encrypted word is well formed, and its last-bit modification is a
distinct, well-formed pair with the same nonce and the flipped masked payload. -/
private theorem cca2Cipher (n : ℕ) (hn : 0 < n) (k m : Fin n → Bool)
    (r : (prfFixedScheme F E hE hFE).enc.Coins n) :
    ∃ x : Fin n → Bool,
      List.ofFn ((prfFixedScheme F E hE hFE).encryptAt n (List.ofFn k) m r) =
        pairEncode (List.ofFn x) (List.ofFn (m + F n k x)) ∧
      List.ofFn (cca2Alter ((prfFixedScheme F E hE hFE).encryptAt n (List.ofFn k) m r)) =
        pairEncode (List.ofFn x) (List.ofFn (cca2FlipBits (m + F n k x))) ∧
      cca2Alter ((prfFixedScheme F E hE hFE).encryptAt n (List.ofFn k) m r) ≠
        (prfFixedScheme F E hE hFE).encryptAt n (List.ofFn k) m r := by
  obtain ⟨x, -, hc⟩ := cca2Encrypt F E hE hFE n k m r
  have hd : 0 < (prfFixedScheme F E hE hFE).ctLen.eval n := by
    rw [prf_ctLen_eval, PRFGame.ctP_eval]
    omega
  have hp : List.ofFn (m + F n k x) ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp only [List.length_ofFn, List.length_nil] at hh
    omega
  refine ⟨x, hc, ?_, cca2Alter_ne hd _⟩
  rw [cca2Alter_ofFn hd, hc, cca2FlipLast_pair _ _ hp, cca2FlipLast_ofFn hn]

/-- Decrypting a pair `⟨x, v⟩` of `n`-bit words under the key `k` unmasks it:
`Dec_k(⟨x, v⟩) = v ⊕ F n k x`, read as an `n`-bit message. -/
private theorem cca2Decrypt (n : ℕ) (k x v : Fin n → Bool)
    (rd : (prfFixedScheme F E hE hFE).dec.Coins n) :
    decodeFin n ((prfFixedScheme F E hE hFE).dec.runAt n
      (pairEncode (List.ofFn k) (pairEncode (List.ofFn x) (List.ofFn v))) rd) =
        some (v + F n k x) := by
  revert rd
  rw [prfFixedScheme_dec, prfScheme_dec]
  intro rd
  rw [runAt_prfDec hE _ n _ _ _ List.length_ofFn List.length_ofFn, hFE, zipWith_xor_ofFn_add,
    decodeFin_ofFn]

/-- At `n > 0`, the valid answer `⟨1, b^n ⊕ e_{n-1}⟩` ends in `!b`. -/
private theorem cca2LastBit {n : ℕ} (hn : 0 < n) (b : Bool) :
    (List.ofFn (Fin.cons (α := fun _ => Bool) true (cca2FlipBits (n := n) fun _ => b))).getLastD
      false = !b := by
  rw [List.ofFn_succ, Fin.cons_zero]
  simp only [Fin.cons_succ]
  rw [← cca2FlipLast_ofFn hn, List.ofFn_const]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [List.replicate_succ', cca2FlipLast_snoc, ← List.cons_append, List.getLastD_concat]

/-- **The attack against any fixed-length scheme.** Let `A = cca2Adversary` run with budget `2`
in `IND_b` under CCA2 with the key `k`. Suppose ciphertexts are nonempty and, for every challenge
`c = Enc_k(b^n)`, every decryption of `c` with its last bit flipped is a message `v` with
`⟨1, v⟩` ending in `!b`. Then `A` outputs `b` with probability one.

**Proof sketch.** Follow the three activations through `buildComp` and `simulate`.
1. On the empty log `A` asks `Challenge ⟨0^n, 1^n⟩`; the oracle samples `re`, answers
   `c = Enc_k(b^n)` (`cca2Messages_choice`) and records it.
2. On the one-entry log `A` asks `Dec` on `c'`, the flip of `c`; `c' ≠ c` (`cca2Alter_ne`), so
   CCA2's `Dec` samples `rd` and answers `⟨1, v⟩`.
3. On the two-entry log `A` outputs `¬(last bit of ⟨1, v⟩) = b`, within the budget.
Each sampled step is averaged by `expect_const`. -/
private theorem cca2Run (S : FixedLengthScheme) (n : ℕ) (hd : 0 < S.ctLen.eval n)
    (b : Bool) (k : List Bool)
    (hdec : ∀ (re : S.enc.Coins n) (rd : S.dec.Coins n), ∃ v : Fin n → Bool,
      decodeFin n (S.dec.runAt n (pairEncode k (List.ofFn
        (cca2Alter (S.encryptAt n k (fun _ => b) re)))) rd) = some v ∧
      (List.ofFn (Fin.cons (α := fun _ => Bool) true v)).getLastD false = !b)
    (r : cca2Adversary.Coins n) :
    ProbComp.prob ((simulate (S.indImpl .cca2 b n k) (cca2Adversary.toComp (S.indCodec n) n 2 r)
      none).bind fun res => .pure (res.1 0)) (· = true) = if b = true then 1 else 0 := by
  obtain ⟨x, hx⟩ : ∃ x : (S.indSpec n).dom 2,
      x = cast (S.indSpec_challengeDom n).symm (cca2Messages n) := ⟨_, rfl⟩
  have h1 : (S.indCodec n).decodeMove
      (cca2Adversary.runAt n ((S.indCodec n).encodeLog []) r) = .query 2 x := by
    rw [MachineCodec.encodeLog_nil, cca2Adversary_run, if_pos rfl,
      FixedLengthScheme.indCodec_decodeMove]
    have hw : List.ofFn x = List.replicate n false ++ List.replicate n true := by
      rw [hx, ofFn_cast (S.inLens_two n).symm, cca2Messages_ofFn]
    rw [← hw]
    exact decodeBitMove_query (S.inLens n) (S.outLens n) 1 2 x
  rw [NUPPT.toComp_eq, buildComp_succ_of_query (next := fun hist => (S.indCodec n).decodeMove
    (cca2Adversary.runAt n ((S.indCodec n).encodeLog hist) r)) h1, simulate_query,
    FixedLengthScheme.indImpl_challenge_none_onSpec]
  have hxc : cast (S.indSpec_challengeDom n) x = cca2Messages n := by
    rw [hx, cast_cast, cast_eq]
  simp only [hxc, cca2Messages_choice, OracleComp.bind_assoc, OracleComp.pure_bind,
    List.nil_append]
  rw [ProbComp.prob_bind]
  refine (congrArg (ProbComp.expect _) (funext fun re => ?_)).trans (ProbComp.expect_const _ _)
  have hne := cca2Alter_ne hd (S.encryptAt n k (fun _ => b) re)
  have h2 : (S.indCodec n).decodeMove (cca2Adversary.runAt n ((S.indCodec n).encodeLog
      [⟨2, x, cast (S.indSpec_challengeRng n).symm (S.encryptAt n k (fun _ => b) re)⟩]) r) =
      .query 1 (cast (S.indSpec_decDom n).symm
        (cca2Alter (S.encryptAt n k (fun _ => b) re))) := by
    simp only [MachineCodec.encodeLog_cons, MachineCodec.encodeLog_nil,
      FixedLengthScheme.indCodec_encodeEntry, cca2Adversary_one,
      FixedLengthScheme.indCodec_decodeMove]
    rw [ofFn_cast (S.outLens_two n).symm, ← cca2Alter_ofFn hd,
      ← ofFn_cast (S.inLens_one n).symm (S.indSpec_decDom n).symm]
    exact decodeBitMove_query (S.inLens n) (S.outLens n) 1 1 _
  rw [buildComp_succ_of_query (next := fun hist => (S.indCodec n).decodeMove
    (cca2Adversary.runAt n ((S.indCodec n).encodeLog hist) r)) h2, simulate_query,
    FixedLengthScheme.indImpl_dec_onSpec]
  have hcc : cast (S.indSpec_decDom n) (cast (S.indSpec_decDom n).symm
      (cca2Alter (S.encryptAt n k (fun _ => b) re))) =
        cca2Alter (S.encryptAt n k (fun _ => b) re) := by
    rw [cast_cast, cast_eq]
  have hopen : (FixedLengthScheme.decOpen .cca2
      (some (S.encryptAt n k (fun _ => b) re)).isSome && !decide
        (some (S.encryptAt n k (fun _ => b) re) =
          some (cca2Alter (S.encryptAt n k (fun _ => b) re)))) = true := by
    simp only [FixedLengthScheme.decOpen_cca2, Option.some.injEq,
      Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    exact fun h => hne h.symm
  rw [hcc, if_pos hopen]
  simp only [OracleComp.bind_assoc, OracleComp.pure_bind]
  rw [ProbComp.prob_bind]
  refine (congrArg (ProbComp.expect _) (funext fun rd => ?_)).trans (ProbComp.expect_const _ _)
  obtain ⟨v, hv, hlast⟩ := hdec re rd
  rw [hv, FixedLengthScheme.decAnswer_some]
  have h3 : (S.indCodec n).decodeMove (cca2Adversary.runAt n ((S.indCodec n).encodeLog
      ([⟨2, x, cast (S.indSpec_challengeRng n).symm (S.encryptAt n k (fun _ => b) re)⟩] ++
        [⟨1, cast (S.indSpec_decDom n).symm (cca2Alter (S.encryptAt n k (fun _ => b) re)),
          cast (S.indSpec_decRng n).symm (Fin.cons (α := fun _ => Bool) true v)⟩])) r) =
      .ret fun _ => b := by
    simp only [List.singleton_append, MachineCodec.encodeLog_cons, MachineCodec.encodeLog_nil,
      FixedLengthScheme.indCodec_encodeEntry, cca2Adversary_two,
      FixedLengthScheme.indCodec_decodeMove]
    rw [ofFn_cast (S.outLens_one n).symm, hlast, Bool.not_not]
    have hb : [b] = List.ofFn (fun _ : Fin 1 => b) := by
      rw [List.ofFn_const, List.replicate_one]
    rw [hb]
    exact decodeBitMove_ret (S.inLens n) (S.outLens n) 1 _
  rw [buildComp_zero_of_ret (next := fun hist => (S.indCodec n).decodeMove
    (cca2Adversary.runAt n ((S.indCodec n).encodeLog hist) r)) h3, simulate_pure,
    OracleComp.pure_bind, ProbComp.prob_pure]

/-- **Claim 169.a: the §3.9 scheme is not CCA2-secure** [PS10, §7.1.3, p. 169], whatever the
family `F`. Some adversary, with a constant query budget, has advantage `1` at every `n > 0`.

The source's attack asks `Dec` for "`c + 1`", the challenge plus one. Read as an exclusive-or with
a fixed nonzero string, it flips the last bit of the challenge. The result is a different, still
well-formed ciphertext, which CCA2's `Dec` therefore answers.

**Proof sketch.**
1. The machine `A` reads its log. With an empty log, it asks the challenge on `⟨0^n, 1^n⟩`. With
   one entry, the challenge answer `c`, it asks `Dec` on `c` with its last bit flipped. With two
   entries, the second a `Dec` answer `⟨v, m'⟩`, it outputs `¬ m'_{n-1}`. It is polynomial-time
   (`NUPPT.ofPolyTimeUniform`); its query budget is `2`, so the third activation's output is read.
2. In `IND_b` the challenge is `c = ⟨r, b^n ⊕ f_k(r)⟩`. For `n > 0` its last bit lies in the
   second component, so the flipped string `c'` is `⟨r, b^n ⊕ e_{n-1} ⊕ f_k(r)⟩`: well-formed,
   and not `c`. CCA2's `Dec` answers `⟨1, b^n ⊕ e_{n-1}⟩` (`runAt_prfDec`).
3. So, for every key and all coins, `A` outputs `b` (`cca2Run`): `IND_b` accepts with probability
   `1` if `b = 1` and `0` if `b = 0`, and the advantage is `|0 − 1| = 1`. -/
theorem prfFixedScheme_not_cca2 :
    ∃ (A : NUPPT) (q : PolyExpr), ∀ n, 0 < n →
      advantage ((prfFixedScheme F E hE hFE).indGame .cca2 A (q.eval n) false n)
        ((prfFixedScheme F E hE hFE).indGame .cca2 A (q.eval n) true n) = 1 := by
  refine ⟨cca2Adversary, .const 2, fun n hn => ?_⟩
  have hd : 0 < (prfFixedScheme F E hE hFE).ctLen.eval n := by
    rw [prf_ctLen_eval, PRFGame.ctP_eval]
    omega
  have hacc : ∀ b : Bool, accept ((prfFixedScheme F E hE hFE).indGame .cca2 cca2Adversary
      ((PolyExpr.const 2).eval n) b n) = if b = true then 1 else 0 := by
    intro b
    rw [PolyExpr.eval_const, accept_eq, FixedLengthScheme.indGame_eq, ProbComp.prob_bind]
    refine (congrArg (ProbComp.expect _) (funext fun rg => ?_)).trans (ProbComp.expect_const _ _)
    obtain ⟨kv, hk⟩ := cca2Gen F E hE hFE n rg
    rw [ProbComp.prob_bind]
    refine (congrArg (ProbComp.expect _) (funext fun r => ?_)).trans (ProbComp.expect_const _ _)
    rw [hk]
    refine cca2Run _ n hd b _ (fun re rd => ?_) r
    obtain ⟨xr, -, hc, -⟩ := cca2Cipher F E hE hFE n hn kv (fun _ => b) re
    refine ⟨cca2FlipBits (fun _ => b), ?_, cca2LastBit hn b⟩
    rw [hc, cca2Decrypt, cca2FlipBits_unmask]
  rw [advantage_eq, hacc, hacc]
  norm_num

/-- **The §3.9 scheme is not CCA2-secure** in the sense of Definition 168.1: an advantage equal
to `1` at every positive `n` is not negligible (Claim 169.a). -/
theorem not_prfFixedScheme_cca2 : ¬ (prfFixedScheme F E hE hFE).INDSecure .cca2 := by
  intro h
  rw [FixedLengthScheme.INDSecure_iff] at h
  obtain ⟨A, q, hA⟩ := prfFixedScheme_not_cca2 F E hE hFE
  obtain ⟨ε, hε, hle⟩ := h A q
  rw [negligible_iff] at hε
  obtain ⟨n₀, hn₀⟩ := hε 0
  have h1 := hn₀ (n₀ + 1) (by omega)
  have h2 := hle (n₀ + 1)
  rw [hA (n₀ + 1) (by omega)] at h2
  simp only [pow_zero, div_one] at h1
  linarith [le_abs_self (ε (n₀ + 1))]

end TCSlib.Cryptography.Composability
