## ===== briefs/pass-shelat-ch5-8/gates/13-padded-cpa/pack.md =====

# Gate 13 · public-key CPA bridge proof (`padded_cpa`)

Round 1. Auditor Codex (Seyoon's choice, 2026-11-11). Draft
[PR #288](https://github.com/Shilun-Allan-Li/tcslib/pull/288) at
`892a3f3c78abcde8bdf822a3b4168ab3302b4272` on branch `land/pass-shelat-padded-cpa`, targeting
`cryptography/pass-shelat-ch2-4` on base `2950c4a74c45b98185a5eaf4601cf8b88a7528c2`. That base
has the post-#286 Lean content `ed0f7238`; later base commits are records only.

This proof audit covers the formerly admitted
`BitPublicKeyScheme.SingleBitSecure.padded_cpa` (`Encryption/PublicKey/OracleSecurity.lean`)
and the two new helper modules `OracleSecurity/ChallengeSim.lean` and
`OracleSecurity/RecordHandler.lean`. The statement passed Gate 04. The issued fill brief, in the
bundle, fixes the route and discipline. The source is [PS10], R. Pass and a. shelat, *A Course in
Cryptography*, third edition, January 2010: Definition 171.5 and the claim after it (book
pp. 171–172).

## The proof

The proof establishes an exact identity, at every `n`:
`advantage(IND_0, IND_1) = distAdv(⟨pk, Enc_pk(0)⟩, ⟨pk, Enc_pk(1)⟩, D)`. Check the steps
independently:

1. **Eager coins.** `expect_simulate_indImpl_cpa` swaps the lazily sampled challenge coins for
   coins sampled up front. Check the induction, and check that coins drawn but never used
   marginalize out.
2. **First-challenge congruence.** `chRun_congr` and `firstQ` show that the run depends on the
   challenge answer only through the first challenge query, and that `firstQ` does not depend on
   the answer function.
3. **The recording handler.** `recHandler`, with `seedLen 0`, three state bits, `Dec` answered
   `00`, every challenge answered `padCt L(n) c`, and the first query recorded. Its `out` returns
   `[a]`, `[¬a]` or `[0]`. It is fed to `Games.exists_handlerMachine` (T1, proved in #285) with
   `k = 2`.
   - Check codec alignment: `recDin`/`recDout` against `inLens`/`outLens`, and the transport
     `chRun_toCompOn_transport`.
   - Check the coin transport `NUPPT.coinsCongr (padEnc_coins …)`, T1's coin equivalence and the
     empty seed.
4. **The identity.** `padded_cpa_advantage_eq` and the pointwise case split
   `expect_indicator_sub` over `(0,1)`, `(1,0)`, equal messages, and no challenge.
   - Check repeated challenges, budget `q = 0` and the timeout output.

## Interfaces and discipline

- **Statement freeze.** The target header and every older declaration must be unchanged; 41 new
  public declarations are added.
- **Rule 10.** No touched declaration may read another file's definition. The brief allows
  `OracleSecurity.lean`'s own definitions to be crossed. The new helper modules are separate files
  and must not unfold `OracleSecurity` (they do not import it) or any other file's definitions.
- **API quality.** Check names, docstrings with formulas, proof sketches, the absence of
  `@[simp]`, and the precise imports.
- **Recorded follow-up debt, not findings of this gate unless you disagree with the
  disposition:**
  - the generic `ProbComp` lemmas left in `ChallengeSim` (DL-30);
  - the `ofFn_padFin_of_length` copies (DL-31).
- **Landing edits.** The maintainer's landing-edit commit must change no statement and no proof
  route.

## Evidence

- `worker-report.md`: the Claude worker's final report.
- `review.md`: the maintainer's independent delivery review.
- `verification.zip`: the review's raw evidence, run on the issue base before the landing edits:
  - integrity and a fresh build (233/233);
  - the admission census (31 → 30) and the statement comparison;
  - axioms;
  - whole-file closure seals of all three files with a base control;
  - 17 controls and the explicit-reader scan.
- `landing/`: on this PR's head:
  - `closure-build.jsonl`: a fresh build of the 233-module closure, 0 errors;
  - `root-checks.jsonl`: the downstream modules through `TCSlib` and `Checks` on the full tree;
  - `axioms.log`: `padded_cpa` and `TrapdoorCollection.tdpBitScheme_padded_cpa` print
    `[propext, Classical.choice, Quot.sound]`.
- `sources.zip`: the 151-module source closure at the head.

## Findings delivery

Return `gate13-padded-cpa-findings.md` as a Markdown file in this chat. For multiple evidence
files, return a ZIP. The user dispatches and merges.

| # | Severity | File and declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

Severities:
- **blocker:** a false or unusable statement, or a scope violation;
- **major:** an incomplete argument, a forbidden new read in a touched declaration, a statement
  change, or necessary evidence that cannot be verified;
- **minor:** documentation or API defects;
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero
majors.

## ===== briefs/pass-shelat-ch5-8/gates/13-padded-cpa/review.md =====

# padded-cpa · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS** (0 blockers, 0 majors, 4 minors, 3 notes).

Delivery: Claude worker, exchange `dffc2e7d` (`inbox/fills/padded-cpa/`), proof-branch tree
`be2bdbb2` (4 patches on `4a09f3993eb9344fc5714610e41ab141a0144db8`). Independent review on a
fresh worktree and a fresh olean tree; evidence `review-evidence.zip` (SHA-256
`f294ca6feebc0b9e2eee7d5581da58f3d5cd23008a0279632c3b57cb9bd2f0b9`; inner `SHA256SUMS`
`85eabe28931c472bc8a18cccebf825abd2c48c4d6f3eae1f2ce0848bd25d1b2c`, 351 entries, pins in
`PROVENANCE.txt`).

## Checks (all re-run by the reviewer)

- Integrity: `PAYLOAD-SHA256SUMS` 63/63; `git am` reproduces `src/` byte for byte and the
  worker's tree; diff 3 files, +889/−12.
- Build: the 233-module final order (the issued 221 plus 12 insertions, topologically sound,
  roots unchanged) 233/233 rc 0, 0 errors; the touched modules and `TrapdoorCPA` warning-free.
- Admissions 31 → 30 (only `padded_cpa`). Statements: 41 public ADDED, 0 CHANGED, 0 REMOVED;
  the target header byte-identical.
- Axioms: `padded_cpa` and `TrapdoorCollection.tdpBitScheme_padded_cpa` print
  `[propext, Classical.choice, Quot.sound]`; no new declaration uses another axiom.
- Rule 10: whole-file seals of all three files over their full TCSlib import closures
  (2,100 / 669 / 2,006 requests) rc 0 with 0 errors; base control clean; neither helper imports
  `OracleSecurity`. Controls 17/17 negatives fail once sealed, positives and unsealed pass.
  Explicit-reader scan: 388 items, 0 foreign definitions.
- Lint 0 FAIL (same 6 WARN as base, untouched files). Trial merges onto the campaign and #286
  textually clean.

## Findings and dispositions

| # | Severity | Finding | Disposition |
|---|---|---|---|
| 1 | minor | `ChallengeSim.expect_sample_prod` repeats `Bridge.expect_sample_pair`'s proof; the report said "duplication: none". | **Landing edit:** proved from `Bridge.expect_sample_pair` (+ import `Games.Bridges.Experiments`). |
| 2 | minor | Generic `ProbComp` lemmas (`expect_sample_equiv/_comm/_unique`, `expect_sub`) published as `ChallengeSim.*`; unscoped `open ChallengeSim ProbComp`. | **Landing edit:** the `open` is scoped to `section PaddedCPA`. Promotion of the four lemmas to `Games/Probability.lean` is recorded as follow-up debt. |
| 3 | minor | `RecordHandler` uses `GGMRed.ofFn_padFin_of_length` via a transitive import; the fact has three copies. | Recorded as follow-up debt: promote `ofFn_padFin_of_length` beside `padFin` in `Asymptotic/Adversary.lean` and re-point. |
| 4 | minor | REPORT cites `evidence/seal/candidates.txt`, absent from the payload. | Recorded; the reviewer's independent seal supersedes it. |
| 5 | note | `OracleSecurity.lean` at 976 lines; the docstring did not name the helper modules. | **Landing edit:** helpers named under "Main results". Further growth triggers a split. |
| 6 | note | The new proofs cross `OracleSecurity`'s own `outLens` (in a private statement), `padded`, `indCodec` definitionally. | Allowed by the brief (own file); disclosed. |
| 7 | note | `chRun_toCompOn_transport` stated its formula only in words. | **Landing edit:** formula stated. |

## Landing

Landing branch `land/pass-shelat-padded-cpa` on the campaign head (Lean `ed0f7238`, after
#286): the worker's 4 commits plus one maintainer landing-edit commit. A fresh build of the
233-module closure on that head runs before the PR is opened.

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

## ===== briefs/pass-shelat-ch5-8/fills/padded-cpa/issued-r1/brief.md =====

# Claude fill · public-key CPA bridge (`padded_cpa`)

**Issue base** `4a09f3993eb9344fc5714610e41ab141a0144db8` on `cryptography/pass-shelat-ch2-4`
(the merge of #284 and #285; later campaign commits are records only).
**Unit** `padded-cpa`. **Worker** Claude. **Lean** 4.25.0 and the Mathlib revision in that
commit's `lake-manifest.json`.

Prove the admitted theorem `BitPublicKeyScheme.SingleBitSecure.padded_cpa` in
`TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean`: single-bit security of a
ch. 2–4 public-key scheme gives IND-CPA security of its padded fixed-length form
[PS10, Definition 171.5 and the claim after it, book pp. 171–172]. It is the CPA dependency of
the first catalog route. `TrapdoorCollection.tdpBitScheme_padded_cpa`
(`PublicKey/TrapdoorCPA.lean`) inherits it. The statement passed Gate 04. The shared machine
reduction T1 (`Games.exists_handlerMachine`) it needs was proved in #285.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4` and start a local branch `fill/padded-cpa` at the exact
  issue base above. Record the base in `REPORT.md`. Keep the local branch at that ancestry.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/padded-cpa/` on
  `exchange/pass-shelat-ch5-8`. Include `REPORT.md`, `patches/` containing the whole
  `git format-patch` series from the issue base, `src/` with the owned paths, and `evidence/`.
  Use commit messages `fill padded-cpa: checkpoint N` and `fill padded-cpa: final`. Pull the
  exchange with rebase before pushing. Push only your delivery path; never force-push. Keep the
  proof branch local. Campaign changes land by a maintainer PR for Seyoon's approval.

## Target

The source declaration is frozen. This quote comes directly from the issue base (line 697).

```lean
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.padded_cpa
    {S : BitPublicKeyScheme} (h : S.SingleBitSecure) (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (b : Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]) re).length + 2
        ≤ L.eval n)
    (hmsg : ∀ n, 1 ≤ L.eval n) : (S.padded L hL hmsg).INDSecure .cpa := by
  sorry
```

Write `S' := S.padded L hL hmsg` below. Its messages are one bit (`msgLen = .const 1`), its
ciphertexts `L(n)` bits. The CPA game `S'.indGame .cpa A q b n` samples key-generation coins and
`A`'s coins and simulates `A` against `Dec` (always `⊥` under CPA) and `Challenge` (encrypts
`m_b` with fresh coins on the first query `⟨m₀, m₁⟩` and repeats the recorded ciphertext
afterwards).

## Published interfaces

Read every definition of another file through these published lemmas (policy §1, rule 10).
`OracleSecurity.lean`'s own definitions (`padCt`, `isPadded`, `padEncFun`, `padDecFun`,
`FixedLengthPKScheme`, `ofPadded`, `padded`, `inLens`, `outLens`, `indImpl`, `indCodec`,
`indGame`, `INDSecure`) may be unfolded, but prefer their readers.

| Interface | Provider |
|---|---|
| `padCt_eq`, `length_padCt`, `pairFstD_padCt`, `isPadded_padCt`, `padEncFun_eq`, `padEnc_coins`, `runAt_padEnc`, `BitPublicKeyScheme.padded_msgLen/_ctLen/_gen/_enc/_dec`, `inLens_zero/_one`, `outLens_zero/_one`, `indSpec_eq`, `indSpec_dom/_rng`, `indImpl_dec_cpa`, `indImpl_challenge_none(_onSpec)`, `indImpl_challenge_repeat(_onSpec)`, `indCodec_decodeMove`, `indCodec_encodeEntry`, `indCodec_timeout`, `indGame_eq`, `INDSecure_iff` | `Encryption/PublicKey/OracleSecurity.lean` (owned) |
| `BitPublicKeyScheme.singleBitSecure_iff`, `pkEncDist_eq` | `Encryption/PublicKey/EnsembleSecurity.lean` |
| `FixedLengthScheme.splitHalf` and its readers, `decOpen_cpa`, `decAnswer` | `Encryption/PrivateKey/OracleSecurity.lean` |
| `Games.exists_handlerMachine` (T1); `PolyHandler.input_eq`, `advInput_eq`, `result_eq`, `answer_of_pairDecode_eq_some/_none`, `answer_of_run_eq`, `impl_apply`, `bitSpecAt_eq`, `seedIn_eq` | `Games/Efficiency.lean` |
| `NUPPT.distinguisherL_eq` | `Asymptotic/Adversary.lean` |
| `NUPPT.runAt_eq`, `coinLen_eq`, `runAtL_eq_output_layout`, `exists_comp` and the closure combinators | `Complexity/Randomized/PPT.lean`, `NonUniform.lean`, `Closure.lean` |
| `NUPPT.toCompOn_eq`, `toCompOn_costBoundedBy`, `buildComp` case equations | `Games/Machines.lean` |
| `bitCodec_decodeMove`, `bitCodec_encodeEntry`, `bitCodec_timeout`, `decodeBitMove_*` | `Games/BitCodec.lean` |
| `simulate` equations and `OracleComp` pure/bind/query laws | `Games/Simulate.lean`, `Games/OracleComp.lean` |
| `accept_eq`, `advantage_eq`, `advantage_comm`, `prob_*`, `expect_*`, `sample_eq`, `dist_apply` | `Games/Advantage.lean`, `Games/Probability.lean` |
| `Bridge.distAdv_eq`, `acceptProb_eq`, `acceptGame_eq`, `prob_sample_pair`, `expect_sample_pair` | `Games/Bridges/Experiments.lean` |
| `abs_prob_sub_le_of_agree`, `prob_split`, identical-until-bad lemmas | `Games/Hopping.lean` |
| `Negligible.mono` and the negligible-function API | `Foundations/Negligible.lean` |
| `pairDecode_pairEncode`, `pairFstD_pairEncode`, `pairSndD_pairEncode`, `length_pairEncode`, `decodeFin_ofFn`, `padFin` readers | `Complexity/TuringMachine/Encoding.lean`, `Asymptotic/Adversary.lean` |

`NUPPT.Coins`, `bitSpecAt`, `bitSpec`, `QueryImpl`, `OracleSpec.add` and `indSpec` are
abbreviations; `PolyExpr.eval` is notation. If a needed equation has no published reader,
record it in `REPORT.md` and use the escalation route below; do not unfold the foreign
definition.

## Proof route and checkpoints

The sketch in the docstring is the route. The intended identity is exact, not only a bound:
for the distinguisher `D` built below, at every `n`,

`advantage (S'.indGame .cpa A q false n) (S'.indGame .cpa A q true n) =
  distAdv (S.pkEncDist n false) (S.pkEncDist n true) (D.distinguisherL n)`.

Then `singleBitSecure_iff` gives a negligible right side, and `INDSecure_iff` closes the goal
with `ε` that right side.

1. **Eager challenge coins.** Under CPA the oracle state only records the challenge. Prove that
   simulating `S'.indImpl .cpa b n pk sk` from `none` has the same output distribution as first
   sampling encryption coins `re`, then simulating the deterministic oracle that answers the
   first challenge with `padFin _ (S'.enc.runAt n ⟨pk, m_b⟩ re)` (same state discipline). This is
   the lazy-to-eager step; prove it by induction on the computation, using the sampling and
   bind laws (`expect_bind`, `expect_sample`, `prob_bind`). Unused coins marginalize out. If a
   generic "sampling commutes with an independent simulation" lemma is missing, prove it as a
   helper (see Scope). Send checkpoint 1.
2. **First-challenge congruence.** For a deterministic challenge answer `g : messages → ciphertext`,
   the simulation's result depends on `g` only through `g (mm⋆)`, where `mm⋆` is the first
   challenge query (or not at all when there is none), and `mm⋆` does not depend on `g`. State it
   for the deterministic simulation of step 1 and prove it by induction. This replaces the
   informal "conditioning on `A`'s choice". Send checkpoint 2.
3. **The distinguisher `D` (T1).** Apply `Games.exists_handlerMachine` with `k = 2`, `din`/`dout`
   chosen so that `(fun i => (din i).eval n) = S'.inLens n`, `(fun i => (dout i).eval n) =
   S'.outLens n`, `dα = .const 1`, and a handler `H` with:
   - `seedLen = .const 0`; `advIn ⟨1^n, ⟨z, ω⟩⟩ = pairFstD z` (the public key of `z = ⟨pk, c⟩`);
   - a state that records whether a challenge was asked and its two message bits;
   - `Dec` answers all-`false` (as `indImpl_dec_cpa`); `Challenge ⟨m₀, m₁⟩` answers
     `padCt L(n) (pairSndD z)` at width `L(n)` and records `⟨m₀, m₁⟩` on the first query;
   - `out` returns `[a]` when the recorded pair is `(0, 1)`, `[!a]` when it is `(1, 0)`, and
     `[false]` when the pair is equal or no challenge was asked.

   All four functions must be polynomial-time; build them from the closure combinators and the
   pairing/padding lemmas already used in `OracleSecurity.lean` (`polyTimeComputable_isPadded`,
   `polyTimeComputable_padEncFun`). **Codec alignment** is a known obligation: T1 states its
   simulation with `bitCodec (fun i => (din i).eval n) …` while `indGame` uses
   `S'.indCodec n = bitCodec (S'.inLens n) (S'.outLens n) 1`. Choose `din`/`dout` so the two are
   definitionally equal if possible; otherwise transport along the propositional equality
   once, in a helper. Send checkpoint 3.
4. **The identity.** Fix `n`, key coins and `A`'s coins. By steps 1–2, game `b`'s output is `A`'s
   bit when the challenge is answered with `Enc(m⋆_b)`. By T1, `D`'s output on
   `⟨pk, Enc_pk(β)⟩` is `A`'s bit with the challenge answered by `Enc(β)`, post-processed by `out`.
   The pointwise case split on `mm⋆ ∈ {(0,1), (1,0), equal, none}` gives equal differences
   (for `(1, 0)` both sides are `A(Enc 1) − A(Enc 0)`). Transport coins: `S'.enc.Coins n` versus
   `S.enc.Coins n` (`padEnc_coins`), and `D`'s coins `φ (ω, r)` with the empty seed. Read
   `distAdv` with `Bridge.distAdv_eq` and `NUPPT.distinguisherL_eq`. Send checkpoint 4, then
   the final payload.

Check the edge cases: a run with no challenge query; repeated challenge queries (the repeat
returns the recorded ciphertext, which `H` reproduces because its answer depends only on `z`);
budget `q = 0`; and the timeout output `zeroBits 1`.

## Scope and proof discipline

- Own `TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean`. Replace the one proof body
  and add helpers there. Helper modules are permitted under
  `TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/` if they are generic (they must not
  import `OracleSecurity`, which would be a cycle) and imported precisely by it. Keep every file
  below 1000 lines. If the proof cannot fit without moving the theorem to a new module, stop and
  escalate with a proposal: moving a statement needs a ruling.
- You may edit the target's proof sketch to describe the proof actually delivered. Preserve the
  statement, every other declaration, the statement prose in docstrings and the global simp
  attributes. New helpers are public only when another file needs them; each public helper
  gets a docstring with its formula and a proof sketch when nontrivial (policy §3).
- Use published readers for other files' definitions in tactics and in term elaboration, including
  generated matchers and projections. For core and Mathlib use their equation lemmas in `simp`,
  `rw` and `unfold`.
- Do not edit `TrapdoorCPA.lean` or any other file outside the owned paths.
- **Escalation.** If the target appears false, or a required reader is missing with no clean
  route, write the exact failing obligation and the smallest proposed correction in `REPORT.md`
  and push a checkpoint. At a partial delivery identify each remaining admission and the
  checked frontier.

## Checks and report

- Bootstrap from `order.txt` and the narrow `roots.txt` using the environment addendum. Insert any
  new helper module before its consumer and recalculate roots if imports change. Check one module
  per `scripts/lean_check_tree.sh` invocation; one Lean process per olean tree.
- Recheck `PublicKey/OracleSecurity` and `PublicKey/TrapdoorCPA`, then sweep the rest of the
  supplied order (it includes every module downstream of the owned file). Compare `sorry` warnings
  with `base-sorries.txt`: the only change must be the removed `padded_cpa`.
- Print the axioms of `padded_cpa` (only `propext`, `Classical.choice`, `Quot.sound`) and of
  `TrapdoorCollection.tdpBitScheme_padded_cpa` (report exactly what it prints; it may inherit
  admissions from other providers).
- Collect foreign references from the elaborated new proofs, including generated matcher and
  projection helpers. Run an instance-aware seal of the touched declarations with the full
  candidate list, plus a control that passes before sealing and fails after sealing. Report the
  candidates, controls and any findings. Include the explicit-unfold scan and
  `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Encryption/PublicKey --check8b`.
- Report the issue base, the target's status, exact changed files and sketch edits, new helper
  declarations, any reader requests, and the resource, cache, bootstrap, sweep, axioms, seals and
  lint evidence.

**Ready to dispatch**

## ===== briefs/pass-shelat-ch5-8/gates/13-padded-cpa/worker-report.md =====

# Fill report · `padded-cpa` · final

**Worker** Claude (external fill, exchange push route). **Issue base**
`4a09f3993eb9344fc5714610e41ab141a0144db8` on `cryptography/pass-shelat-ch2-4`. **Proof branch**
local `fill/padded-cpa` at `24747c9d8` (4 commits over the base; never pushed). **Pack** read at exchange
`cc07d65f9`; `sha256sum -c SHA256SUMS` in `outbox/fills/padded-cpa/`: all 7 OK. Source hashes:
`sha256sum -c SOURCE-SHA256SUMS` from a clean base worktree, 221/221 OK
(`evidence/logs/source-sha256.log`).

## 1. Result

**`BitPublicKeyScheme.SingleBitSecure.padded_cpa` is proved.** No admission remains in the
touched files. The frozen statement is unchanged (diff of the declaration: body only). Axioms:
`[propext, Classical.choice, Quot.sound]`.

The proof follows the brief's route and proves the exact identity, not only a bound: for the
machine `D` of T1, at every `n`,
`advantage (S'.indGame .cpa A q false n) (S'.indGame .cpa A q true n) =
distAdv (S.pkEncDist n false) (S.pkEncDist n true) (D.distinguisherL n)`
(`padded_cpa_advantage_eq`); then `singleBitSecure_iff` and `INDSecure_iff` close the goal with
`ε` the right side.

| Brief step | Delivered as |
|---|---|
| 1 eager challenge coins | `expect_simulate_indImpl_cpa` (private, `OracleSecurity.lean`): for every `G`, `𝔼[G ∘ fst]` of the lazy simulation from any state equals `𝔼_re` of `G` of the deterministic run `ChallengeSim.chRun` with challenge answer `Enc(m_b; re)`. Induction on the computation; the unused coins marginalize out by `chRun_some_congr` and `expect_const`. |
| 2 first-challenge congruence | `ChallengeSim.chRun_congr`: `chRun g c none = chRun g' c none` whenever `g, g'` agree at the first challenge query `firstQ c` (vacuous without one); `firstQ` does not mention `g`. Induction. |
| 3 distinguisher `D` (T1) | `Games.exists_handlerMachine` with `k = 2`, `din = recDin L = [L, 2]`, `dout = recDout L = [2, L]`, `dα = .const 1`, and `H = ChallengeSim.recHandler L (cpaAns L) _`: `seedLen = 0`, state `[asked, m₀, m₁]` (initially `000`), `advIn ⟨1^n, ⟨z, ω⟩⟩ = pairFstD z`, `Dec` answered `00`, every challenge answered `padCt L(n) (pairSndD z)` with the first query recorded, `out` = `[a]` for `(0,1)`, `[¬a]` for `(1,0)`, `[0]` otherwise. All four functions are built from the closure combinators (`polyTimeComputable_recRun`, `polyTimeComputable_recOut`, `polyTimeComputable_cpaAns` as `polyTimeComputable_padEncFun`). Its simulation is `chRun` with the constant answer, with final state `firstQ` (`simulate_recHandler_init`). |
| codec alignment | `din/dout` evaluate to `S'.inLens n`/`S'.outLens n` only propositionally (`hins`, `houts`, by the published `inLens_*`, `outLens_*`, `padded_*`, `PolyExpr.eval_const`). The transport is done once, generically, by `subst` (`ChallengeSim.chRun_toCompOn_transport`, also over `dα.eval n = 1`). |
| 4 identity | `padded_cpa_advantage_eq`: game side by step 1, step 2 and the coin transport `NUPPT.coinsCongr (padEnc_coins …)`; `D` side by `Bridge.acceptProb_eq`, T1's `φ` (`expect_sample_equiv`), the empty seed (`expect_sample_unique`), and `NUPPT.distinguisherL_eq`; the pointwise case split on `(m₀, m₁)` is `ChallengeSim.expect_indicator_sub`. |

**Edge cases.** The computation is treated abstractly, so the proof is uniform in the budget
(`q = 0` included) and in the codec's timeout output `zeroBits 1`, which is just `A`'s output
value on both sides. A run with no challenge query is the `firstQ = none` branch (both games
equal, `D` outputs `[0]`: `recOut_init`). Repeated challenge queries return the recorded
ciphertext in the game (`indImpl_challenge_repeat`, `chRun_query_one_some`) and the same
`padCt L(n) c` in `H` (`recRun_recorded`, `simulate_recHandler_recorded`).

**Checkpoints.** Steps 1–4 were completed together; checkpoint 1 (exchange `482bfaa57`) already
carried the complete proof (proof-branch `747b9c2a7`). Commit 4 then removed the definitional
readings that the seal found (§5) without changing the route.

## 2. Changed files and declarations

`git diff --stat 4a09f399..24747c9d8`: 3 files, 889 insertions, 12 deletions.

| File | Lines | Change |
|---|---|---|
| `TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean` (owned) | 705 → 976 | 3 imports added; new private section before the target; target body; target sketch; one status phrase in the module docstring |
| `…/PublicKey/OracleSecurity/ChallengeSim.lean` (new helper) | 273 | generic: deterministic CPA run, first query, congruence, transport, sampling identities |
| `…/PublicKey/OracleSecurity/RecordHandler.lean` (new helper) | 333 | generic in `Lc` and `ans`: the recording `PolyHandler` and its simulation |

Both helpers import neither `OracleSecurity` nor anything downstream of it; `OracleSecurity`
imports both explicitly. All files are below 1000 lines. Statements, other declarations, the
statement prose and global simp attributes are unchanged. **Sketch edits:** the target's
`**Proof sketch.**` was rewritten to describe the delivered proof (eager coins, congruence, the
recording handler, the exact identity); the module docstring's "Main results" line lost
"(stated; a `sorry` under its sketch)".

**New imports of `OracleSecurity`:** `Games.Bridges.Experiments` (`Bridge.acceptProb_eq`,
`acceptGame_eq`), `…OracleSecurity.ChallengeSim`, `…OracleSecurity.RecordHandler` (which imports
`Games.Efficiency` for T1 and `Complexity.ClassNP.PolyTimeBlockLoop` for `headD`, `tail`, `not`).

**New public declarations** (each with a docstring stating its formula, and a sketch when
nontrivial; definitions with case or `_eq` lemmas, the structure with `simps` field equations):
- `ChallengeSim` (namespace `TCSlib.Cryptography.Composability.ChallengeSim`): `chRun` (+
  `chRun_pure`, `chRun_query_zero`, `chRun_query_one_none`, `chRun_query_one_some`), `firstQ` (+
  `firstQ_pure`, `firstQ_query_zero`, `firstQ_query_one`), `chRun_some_congr`, `chRun_congr`,
  `length_of_firstQ_eq_some`, `chRun_toCompOn_transport`, `expect_sample_equiv`,
  `expect_sample_prod`, `expect_sample_comm`, `expect_sample_unique`, `expect_sub`,
  `expect_indicator_sub`.
- `RecordHandler` (same namespace): `recDin` (+ `_zero`, `_one`), `recDout` (+ `_zero`, `_one`),
  `recRun` (+ `recRun_eq`, `recRun_dec`, `recRun_fresh`, `recRun_recorded`,
  `polyTimeComputable_recRun`), `recOut` (+ `recOut_eq`, `recOut_init`, `recOut_recorded`,
  `polyTimeComputable_recOut`), `recAdvIn` (+ `recAdvIn_eq`), `recHandler` (+ `simps` equations
  `recHandler_stateLen/_seedLen/_init/_run/_advIn/_out`, `isSimp := false`),
  `simulate_recHandler_recorded`, `simulate_recHandler_init`.
- They are public because `OracleSecurity` uses them (helper modules).

**New private declarations in `OracleSecurity.lean`:** `cpaAns` (the challenge answer
`padCt L(n) c` read from the context), `polyTimeComputable_cpaAns`, `cpaAns_seedIn`,
`ofFn_splitHalf_bit`, `expect_simulate_indImpl_cpa` (step 1), `padded_cpa_advantage_eq` (step 4).

**Duplication: none.** A search of `TCSlib` found no existing lemma of the forms of the sampling
identities; the closest is `Bridge.expect_sample_pair` (sequential sampling equals product
sampling), a different statement. **Reader requests: none blocking.** One remark for the shared
layer: the exact-length padding lemma used here is `GGMRed.ofFn_padFin_of_length` (in
`Pseudorandom/Functions/Asymptotic/GGM/Run.lean`); a copy exists in `Asymptotic/HardCoreGLColl`.
Its natural home is beside `padFin` in `Asymptotic/Adversary.lean` (pre-existing duplication, not
introduced here).

## 3. Environment, cache and bootstrap

Preflight (`logs/preflight.log`, before any cache or Lean work):
- `nproc` 4. cgroup v1 (`…/claude-code-bash`): `memory.limit_in_bytes` 14,337,298,432;
  in use = `usage − total_cache + total_shmem` = 4,237,475,840 − 4,073,332,736 + 0 = 164,143,104;
  **headroom 13,516 MiB** (floor 4 GiB). `oom_kill 0`, `failcnt 0` at preflight and at the end;
  peak `max_usage_in_bytes` 12,736,491,520 (includes page cache).
- Clone `/home/user/fill` and scratch `/tmp/claude-0`: `/dev/vda`, ext4 (no tmpfs).
  **26,194,386,944 B free** (floor 12 GiB); re-check before the cache 23,608,496,128 B (floor 8 GiB);
  19,134,824,448 B free at the end.

Toolchain: elan installed after the preflight, `leanprover/lean4:v4.25.0` (Lean 4.25.0,
`cdd38ac5…`) (`logs/toolchain.log`). The proof checkout is a separate worktree of the base
(`/home/user/fill`, local branch `fill/padded-cpa`); `.lake` lives only there.

Cache (`logs/cache-store.log`, `cache-get.log`, `mathlib-roots.txt`, `packages.log`,
`cache-probe.log`):
- Archive store `~/.cache/mathlib` **absent** before the fetch (0 files, 0 bytes); every archive
  was downloaded by this session.
- Narrowed fetch for the **97 roots** (identical to the pack's `roots.txt`) with
  `TAR_OPTIONS=--no-same-owner`: "Attempting to download 2370", "Decompressing 2370", 0 failed,
  exit 0. No zero-size olean. The unfiltered `lake exe cache get` was never run; no `lake build`.
- Packages: the 11 present packages match the manifest's URL and revision; `doc-gen4`,
  `UnicodeBasic`, `BibtexQuery`, `MD4Lean` are ABSENT and imported by no module of the order. Last
  line: `package check: PASS (0 mismatches)`.
- Probe: a file importing the first root elaborated through `scripts/lean_check_tree.sh` (exit 0).

Bootstrap (addendum item 5, owned file's upstream first):
- `logs/bootstrap.log`: the 101 modules of the issued order that `PublicKey/OracleSecurity`
  imported at the base (`logs/bootstrap-upstream.txt`), all exit 0.
- After the new imports (§6): the 46 further modules of the new upstream closure
  (`logs/bootstrap-upstream2.txt`), all exit 0 (`logs/bootstrap2.log`). An earlier attempt to build
  the 10 added T1 modules alone failed only on missing oleans of not-yet-built prerequisites
  (`logs/bootstrap-added.log`, item 8: not findings).
- The rest of the order was built by the final sweep.

Resources: one Lean process at a time throughout (every check through `chk.sh` →
`scripts/lean_check_tree.sh`, sequential; no self-imposed timeouts; start, end, elapsed and the
peak RSS of each check are logged). Peak Lean RSS 3,065 MiB (sweep); longest module 68 s
(`Asymptotic/OneWayYao`). No shortage, no exit 135/137/139, no ENOSPC.

**One interrupted sweep.** The first final sweep was stopped by me after 15 modules to fix the
readings described in §5 (`logs/sweep-aborted-1.log`); the module being checked
(`Build/Primitives`, whose olean the script had removed) was rebuilt before continuing
(`logs/dev-checks.log`). The authoritative sweep is `logs/sweep.log`.

## 4. Checks

Module checks during development: `logs/dev-checks.log` (`ChallengeSim`, `RecordHandler`,
`PublicKey/OracleSecurity`, each one call of `scripts/lean_check_tree.sh`).

**Final sweep** (`logs/sweep.log`, proof-branch `24747c9d8`): all **233 modules of
`order-final.txt` passed, 0 failed**, including `PublicKey/OracleSecurity` and
`PublicKey/TrapdoorCPA` (positions 159–160, rechecked after the two helpers) and every module
downstream of the owned file. The three touched modules have **no error and no warning**.

**Admissions** (`logs/sorry-census.txt`, positions of the `declaration uses 'sorry'` warnings
read back to declaration names): **30**, i.e. `base-sorries.txt` (31) minus exactly
`BitPublicKeyScheme.SingleBitSecure.padded_cpa`; nothing added.

**Axioms** (`logs/axioms.log`, `seal/Axioms.lean`):
- `BitPublicKeyScheme.SingleBitSecure.padded_cpa`: `[propext, Classical.choice, Quot.sound]`.
- `TrapdoorCollection.tdpBitScheme_padded_cpa`: `[propext, Classical.choice, Quot.sound]` (it
  inherits no admission).

**Lint** `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Encryption/PublicKey
--check8b`: before (clean base worktree) 0 FAIL, 6 WARN over 15 files; after 0 FAIL, the same 6
WARN (all in untouched files) over 17 files (`logs/lint-before.log`, `logs/lint-after.log`). The
two helpers and the owned file have no WARN (check 8 and 8b included). No new line exceeds 100
characters.

## 5. Readings: scan, seal, controls, explicit unfolds

- **Scan** (`seal/SealScan.lean`, `logs/seal-scan.log`; adapted from the s2b-efficiency scan).
  Roots: every declaration of the two helpers, the target and the six private helpers of
  `OracleSecurity`: 63 roots, 68 declarations scanned with their auxiliary declarations
  (matchers, `proof_`, `eq_`, internal names).
  - **59 foreign TCSlib definitions; 41 regular (sealable)**, listed in `seal/candidates.txt`:
    `NUPPT.{coinLen, coinsCongr, distinguisherL, runAt, toCompOn}`, `PolyExpr.eval`,
    `PolyTimeComputable`, `pairFstD`, `pairSndD`, `pairEncode`, `pairDecode`,
    `BitPublicKeyScheme.{SingleBitSecure, pkEncDist}`, `FixedLengthScheme.splitHalf`,
    `Bridge.acceptGame`, `OracleComp.bind`, `PolyHandler.{advInput, answer, impl, input, result}`,
    `ProbComp.{expect, prob, sample}`, `accept`, `advantage`, `acceptProb`, `distAdv`,
    `Negligible`, `bitCodec`, `seedIn`, `simulate`, `zeroBits`, `padFin`, and the helper
    definitions `chRun`, `firstQ`, `recDin`, `recDout`, `recOut`, `recAdvIn`, `recHandler`
    wherever another module uses them.
  - **Instances:** the scan records every TCSlib instance in the roots' terms: **none**.
  - **Not sealable (18):** reducible abbreviations, projections and auxiliary recursors, read as
    notation: `NUPPT.Coins`, `ProbComp`, `bitSpec`, `bitSpecAt`, `unifSpec`,
    `OracleSpec.dom/rng`, `BitPublicKeyScheme.gen/enc`,
    `PolyHandler.{advIn, init, out, run, seedLen, stateLen}`, `OracleComp.{casesOn, brecOn, below}`.
- **Sealed copies** (`seal/Seal{ChallengeSim,RecordHandler,OracleSecurity}.lean`, generator
  `tools/mkseal.py`, `logs/mkseal.log`): verbatim copies with every regular foreign definition the
  file's touched declarations use made `local irreducible` (6, 16 and 38 names), each importing
  only the original's imports; for `OracleSecurity` the seal starts at the touched section. **All
  three elaborate with exit 0 and no warning** (`logs/seal.log`).
- **What the seal caught** (fixed in proof-branch commit 4, `logs/seal-dev.log`): three steps of
  `RecordHandler` read `seedIn` (twice) and `PolyExpr.eval` (a length through `List.ofFn` of a
  two-bit vector) by definitional unfolding; a review for the same pattern removed `rfl`/`exact`
  steps through `PolyExpr.eval (.const _)`, `simulate` (pure case) and `chRun` (from
  `OracleSecurity`). All now go through `seedIn_eq`, `PolyExpr.eval_const`, `simulate_pure` and the
  `chRun_*` equations.
- **Controls** (`seal/SealControls{Unsealed,Sealed}.lean`): seven readings through a body
  (`PolyExpr.eval`, `zeroBits`, `padFin`, `seedIn`, `simulate`, `chRun`, `recDin`). **All seven pass
  unsealed and fail sealed** with the full 41-name candidate list (lines 11, 13, 15, 18, 21, 24, 26
  of `SealControlsSealed.lean`), so the seal is active.
- **Explicit-unfold scan** (`tools/rwids.py`, `seal/RwIds*.lean`, `logs/rwids.log`,
  `logs/rwids-files.tsv`). `irreducible` does not block `rw [f]`, `simp [f]` or `unfold f`, so every
  identifier the added lines pass to `rw`, `rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`,
  `dsimp` or `unfold` was resolved in its file's namespace and `open`s: 169 in total
  (38 + 40 + 91).
  - 137 resolve to theorems. The rest are local hypotheses (`h`, `ih`, `hans`, …), the
    dot-notation `S.indImpl_dec_cpa/_challenge_none/_challenge_repeat` (the owned file's own
    theorems), the owned file's private lemmas `cpaAns_seedIn` and `ofFn_splitHalf_bit`, and `rfl`
    (the proof term of a `show (true != false) = true from rfl` rewrite).
  - **The only definition passed is `cpaAns`**, the owned file's own private definition, in
    `polyTimeComputable_cpaAns` and `cpaAns_seedIn`. `padCt` is read through `padCt_eq`. No core,
    Mathlib or foreign TCSlib definition is passed.
- Other conversions: the owned file's own definitions `padded`/`ofPadded`, `indCodec`, `inLens`,
  `outLens` are crossed definitionally in a few `exact`/`:= hq` steps (allowed by the brief for
  `OracleSecurity.lean`'s own definitions; they stay unsealed in the sealed copy).

**Readings disclosed: none of a foreign definition.**

## 6. Order and roots

`OracleSecurity` now imports `Games.Bridges.Experiments` and (through `RecordHandler`)
`Games.Efficiency`, as the brief's interface table requires. Their closure adds **10 modules** that
were not in the issued `order.txt` (`Games/Bridges/{QueryTree, Machines, Experiments}`,
`Games/Efficiency/{Strings, Replay, Handler, OracleBridge, Interactive, InteractiveSpec}`,
`Games/Efficiency`); with the two new helpers, **12 modules** are inserted immediately before
`PublicKey/OracleSecurity`, giving `logs/order-final.txt` (233 modules; `diff` with the issued order
shows exactly these 12 insertions; `tools/topo.py`: every import precedes its importer). None of
the 12 imports anything downstream of `OracleSecurity`. **Roots unchanged**: the 97 Mathlib roots
of the final order equal the pack's `roots.txt` (`logs/mathlib-roots-final.txt`), so no further
cache fetch was needed.

## 7. Payload

**Delivery commits.** The commit `fill padded-cpa: final` (`06bc7b21d`) and checkpoint 1 omitted
`evidence/`: a local Git exclude entry (`evidence/`, added for the proof worktree, which shares
the object store with the exchange checkout) hid it. The exclude entry was removed and the
following commit, also titled `fill padded-cpa: final`, adds `evidence/` and this note; the
delivery is the path at that commit. Nothing else changed: `REPORT.md` differs only by this
paragraph, and `patches/` and `src/` are identical.

`REPORT.md`; `patches/` = `git format-patch 4a09f399..24747c9d8` (4 patches); `src/` = the three
owned paths at `24747c9d8`; `evidence/{logs,seal,tools}`. `PAYLOAD-SHA256SUMS` covers every file. Applying the 4 patches with `git am` to a clean base
worktree reproduces `src/` byte for byte and the proof branch's tree (`logs/patch-reproduce.log`).
Commits on the proof branch:
1. `e952cb383` deterministic CPA challenge run and sampling identities (`ChallengeSim`);
2. `ddcdcd8cf` the recording handler (`RecordHandler`);
3. `747b9c2a7` the proof of `padded_cpa` (checkpoint 1);
4. `24747c9d8` read foreign definitions only through their published lemmas (seal findings),
   `padCt_eq`, line wraps.

**Final payload delivered — ready for maintainer review**

## ===== TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRG
import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
import TCSlib.Cryptography.Encryption.PublicKey.EnsembleSecurity
import TCSlib.Complexity.ClassP.BinaryArith.Loops
import TCSlib.Cryptography.Games.Bridges.Experiments
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.ChallengeSim
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.RecordHandler

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# CPA, CCA1 and CCA2 security of public-key encryption

[PS10, Definition 171.5], the public-key form of Definition 168.1: `(pk, sk) ← Gen(1^n)`;
`(m₀, m₁, state) ← A^{O₁(sk)}(1^n, pk)`; `c ← Enc_pk(m_b)`; output `A^{O₂(sk)}(c, state)`. The
oracle pairs are `[·, ·]` (CPA), `[Dec, ·]` (CCA1) and `[Dec, Dec*]` (CCA2), where `Dec*` answers
every query except the challenge. There is no encryption oracle: the adversary holds `pk`.
The trapdoor application of Claim 172.a is in `Encryption.PublicKey.TrapdoorCPA`.

**Its encoding.** As in the private-key game (`Encryption/PrivateKey/OracleSecurity.lean`), one
machine plays both phases. It takes `pk` and queries the bit-string oracles `Dec` and `Challenge`.
The oracle state records the challenge and uses it to gate `Dec` by phase (`decOpen`).

**Fixed lengths by canonical padding** (ruling of 2026-11-05). The codec's oracles take and return
fixed-length strings. Public-key schemes of the ch. 2–4 layer have ciphertexts of varying length,
for example Algorithm 104.3's `⟨f_i(r), b ⊕ m⟩`. A generic wrapper (`FixedLengthPKScheme.ofPadded`)
pads every ciphertext `c` to `L(n)` bits as `⟨c, 1^{L(n) − 2|c| − 2}⟩` (`padCt`). Its decryptor
answers `⊥` on every string that is not such a canonical padding (`isPadded`). Without that check
the padded scheme would be malleable: changing a padding bit of the challenge gives a different
string that decrypts to the same message, which breaks CCA2. Padding is a bijection between
ciphertexts and canonical strings (`pairFstD_padCt`, `padCt_of_isPadded`). So `Dec*` refusing the
padded challenge is `Dec*` refusing the challenge. A bound `L` always exists
(`PublicKeyScheme.exists_padBound`, from the machines' time bounds).

**Deviations** (beyond those of Definition 168.1): ciphertexts reach the adversary padded, and
`Dec` takes only `L(n)`-bit queries, so it decrypts only ciphertexts with `2|c| + 2 ≤ L(n)`.
Security is stated for each admissible `L`; a larger `L` admits longer `Dec` queries.

## Main definitions

* `Composability.padCt`, `Composability.isPadded`: canonical padding and its test.
* `Composability.FixedLengthPKScheme`: a public-key scheme with `msgLen(n)`-bit messages and
  `ctLen(n)`-bit ciphertexts; `FixedLengthPKScheme.ofPadded` builds one by padding.
* `PublicKeyScheme.padded`, `BitPublicKeyScheme.padded`: the ch. 2–4 schemes, padded.
* `FixedLengthPKScheme.indImpl`, `indGame`, `INDSecure`: [PS10, Definition 171.5].

## Main results

* `pairFstD_padCt`, `isPadded_padCt`, `padCt_of_isPadded`: padding is a bijection onto the
  canonical strings.
* `PublicKeyScheme.exists_padBound`, `BitPublicKeyScheme.exists_padBound`: padding bounds exist.
* `BitPublicKeyScheme.SingleBitSecure.padded_cpa`: single-bit security gives CPA security.
  Its helpers are `OracleSecurity.ChallengeSim` (the deterministic CPA run and first-challenge
  congruence) and `OracleSecurity.RecordHandler` (the recording handler for T1).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.1.4, Definition 171.5 and the claim after it on Construction 104.3 (book pp. 171–172).
-/

namespace TCSlib.Cryptography.Composability

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! ### Canonical padding -/

/-- **Canonical padding** of a ciphertext `c` to `L` bits: `⟨c, 1^{L − 2|c| − 2}⟩`. -/
def padCt (L : ℕ) (c : List Bool) : List Bool :=
  pairEncode c (List.replicate (L - (2 * c.length + 2)) true)

/-- Padding pairs `c` with `L - (2 * c.length + 2)` true bits. -/
theorem padCt_eq (L : ℕ) (c : List Bool) :
    padCt L c = pairEncode c (List.replicate (L - (2 * c.length + 2)) true) := rfl

/-- Whether `w` is a canonical padding: a pair `⟨c, s⟩` whose second part `s` is all `true`. -/
def isPadded (w : List Bool) : Bool :=
  decide (pairEncode (pairFstD w) (pairSndD w) = w) && !BinArith.hasFalse (pairSndD w)

/-- The canonical-padding test checks that `w` is its decoded pair and that its second
component contains no false bit. -/
theorem isPadded_eq (w : List Bool) :
    isPadded w =
      (decide (pairEncode (pairFstD w) (pairSndD w) = w) && !BinArith.hasFalse (pairSndD w)) := rfl

/-- A padding to `L ≥ 2|c| + 2` bits has `L` bits. -/
theorem length_padCt {L : ℕ} {c : List Bool} (h : 2 * c.length + 2 ≤ L) :
    (padCt L c).length = L := by
  simp only [padCt, length_pairEncode, List.length_replicate]
  omega

/-- Unpadding recovers the ciphertext. -/
@[simp] theorem pairFstD_padCt (L : ℕ) (c : List Bool) : pairFstD (padCt L c) = c := by
  simp [padCt]

/-- A padding is canonical. -/
theorem isPadded_padCt (L : ℕ) (c : List Bool) : isPadded (padCt L c) = true := by
  simp [isPadded, padCt, BinArith.hasFalse_eq]

/-- A canonical string is the padding of its first part to its own length. -/
theorem padCt_of_isPadded {w : List Bool} (h : isPadded w = true) :
    padCt w.length (pairFstD w) = w := by
  simp only [isPadded, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨h₁, h₂⟩ := h
  have hall : pairSndD w = List.replicate (pairSndD w).length true := by
    refine List.eq_replicate_iff.2 ⟨rfl, fun b hb => ?_⟩
    cases b
    · simp only [BinArith.hasFalse_eq, List.any_eq_false, List.mem_map, id_eq,
        forall_exists_index, and_imp] at h₂
      exact absurd rfl (h₂ _ false hb rfl)
    · rfl
  have hlen : w.length = 2 * (pairFstD w).length + 2 + (pairSndD w).length := by
    conv_lhs => rw [← h₁]
    simp only [length_pairEncode]
  unfold padCt
  rw [hlen, show 2 * (pairFstD w).length + 2 + (pairSndD w).length -
    (2 * (pairFstD w).length + 2) = (pairSndD w).length by omega, ← hall]
  exact h₁

/-- The canonical test is polynomial-time. -/
theorem polyTimeComputable_isPadded : PolyTimeComputable (fun w => [isPadded w]) := by
  have heq : PolyTimeComputable fun w => [decide (pairEncode (pairFstD w) (pairSndD w) = w)] := by
    convert polyTimeComputable_pairEq.comp
      ((polyTimeComputable_pairFstD.pairEncode polyTimeComputable_pairSndD).pairEncode
        polyTimeComputable_id) using 1
    funext w
    simp [Function.comp_apply]
  exact polyTimeComputable_and heq
    (polyTimeComputable_not (BinArith.polyTimeComputable_hasFalse.comp polyTimeComputable_pairSndD))

/-! ### The padded encryptor and decryptor -/

/-- The padded encryptor's string function: run `Enc` on the same parameter, argument and coins,
and pad its ciphertext to `L(n)` bits. -/
def padEncFun (enc : NUPPT) (L : PolyExpr) (z : List Bool) : List Bool :=
  padCt (L.eval (NUPPT.inParam z).length)
    (enc.output (NUPPT.layout (NUPPT.inParam z) (NUPPT.inArg z) [] (NUPPT.inCoins z)))

/-- The padded encryptor's string function pads the original output at the same parameter,
argument and coins, with empty advice, to the length prescribed by `L`. -/
theorem padEncFun_eq (enc : NUPPT) (L : PolyExpr) (z : List Bool) :
    padEncFun enc L z = padCt (L.eval (NUPPT.inParam z).length)
      (enc.output (NUPPT.layout (NUPPT.inParam z) (NUPPT.inArg z) [] (NUPPT.inCoins z))) := rfl

/-- The padded encryptor is polynomial-time. -/
theorem polyTimeComputable_padEncFun (enc : NUPPT) (L : PolyExpr) :
    PolyTimeComputable (padEncFun enc L) := by
  have ho : PolyTimeComputable fun z =>
      enc.output (NUPPT.layout (NUPPT.inParam z) (NUPPT.inArg z) [] (NUPPT.inCoins z)) :=
    enc.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
      NUPPT.polyTimeComputable_inParam NUPPT.polyTimeComputable_inArg
      (polyTimeComputable_const []) NUPPT.polyTimeComputable_inCoins)
  have h := ho.pairEncode ((polyTimeComputable_pairDropPoly .var).comp
    ((ho.pairEncode (polyTimeComputable_const [])).pairEncode
      ((polyTimeComputable_unaryPoly L).comp NUPPT.polyTimeComputable_inParam)))
  convert h using 1
  funext z
  simp [padEncFun, padCt, Function.comp_apply, length_pairEncode]

/-- The padded decryptor's string function on `⟨sk, w⟩`: `Dec ⟨sk, c⟩` if `w` is the canonical
padding of `c`, and `⊥` otherwise, here `true :: w`, one bit longer than the query. -/
def padDecFun (dec : List Bool → List Bool) (z : List Bool) : List Bool :=
  if isPadded (pairSndD z) then dec (pairEncode (pairFstD z) (pairFstD (pairSndD z)))
  else true :: pairSndD z

/-- The padded decryptor decrypts the unpadded query when its canonical test passes and
returns `true :: pairSndD z` otherwise. -/
theorem padDecFun_eq (dec : List Bool → List Bool) (z : List Bool) :
    padDecFun dec z =
      if isPadded (pairSndD z) then dec (pairEncode (pairFstD z) (pairFstD (pairSndD z)))
      else true :: pairSndD z := rfl

/-- The padded decryptor is polynomial-time when `Dec` is. -/
theorem polyTimeComputable_padDecFun {dec : List Bool → List Bool}
    (hdec : PolyTimeComputable dec) : PolyTimeComputable (padDecFun dec) :=
  polyTimeComputable_ite (polyTimeComputable_isPadded.comp polyTimeComputable_pairSndD)
    (hdec.comp (polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)))
    ((polyTimeComputable_const [true]).append polyTimeComputable_pairSndD)

/-- The padded encryptor as a machine, with the coins of `Enc`. -/
noncomputable abbrev padEnc (enc : NUPPT) (L : PolyExpr) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_padEncFun enc L) enc.coins

/-- The padded encryptor uses the original encryptor's coin polynomial. -/
theorem padEnc_coins (enc : NUPPT) (L : PolyExpr) : (padEnc enc L).coins = enc.coins :=
  NUPPT.coins_ofPolyTimeUniform (polyTimeComputable_padEncFun enc L) enc.coins

/-- The padded encryptor pads the ciphertext of the uniform `Enc` with the same coin string,
read in `enc` through the public `padEnc_coins` identification. -/
theorem runAt_padEnc {enc : NUPPT} (henc : enc.Uniform) (L : PolyExpr) (n : ℕ) (y : List Bool)
    (r : (padEnc enc L).Coins n) : (padEnc enc L).runAt n y r =
      padCt (L.eval n) (enc.runAt n y (NUPPT.coinsCongr (padEnc_coins enc L) n r)) := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform, henc.runAt_eq,
    NUPPT.coinsCongr_ofFn]
  simp only [padEncFun_eq, NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.inCoins_eq,
    NUPPT.layout_eq, NUPPT.advInput_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate]

/-- The padded decryptor on a padding is `Dec`. -/
theorem padDecFun_padCt (dec : List Bool → List Bool) (sk c : List Bool) (L : ℕ) :
    padDecFun dec (pairEncode sk (padCt L c)) = dec (pairEncode sk c) := by
  simp [padDecFun, isPadded_padCt]

/-- The padded decryptor answers a non-canonical query `w` with a string of `|w| + 1` bits. -/
theorem padDecFun_of_not_isPadded (dec : List Bool → List Bool) (sk w : List Bool)
    (hw : isPadded w = false) : padDecFun dec (pairEncode sk w) = true :: w := by
  simp [padDecFun, hw]

/-! ### Fixed-length public-key schemes -/

/-- A **public-key scheme with fixed-length ciphertexts** [PS10, Definition 102.1]: `msgLen(n)`-bit
messages; `Gen(1^n) = ⟨pk, sk⟩`; `Enc_pk(m)` activated on `⟨pk, m⟩`, whose ciphertexts under
generated keys have `ctLen(n)` bits; a deterministic polynomial-time `Dec` on `⟨sk, c⟩`, with
`⊥` any output that decodes to no message; perfect correctness. -/
structure FixedLengthPKScheme where
  /-- The message length. -/
  msgLen : PolyExpr
  /-- The ciphertext length. -/
  ctLen : PolyExpr
  /-- The key generator. -/
  gen : NUPPT
  /-- The encryptor. -/
  enc : NUPPT
  /-- The decryptor. -/
  dec : List Bool → List Bool
  /-- `Gen` is a PPT. -/
  gen_uniform : gen.Uniform
  /-- `Enc` is a PPT. -/
  enc_uniform : enc.Uniform
  /-- `Dec` is polynomial-time. -/
  dec_poly : PolyTimeComputable dec
  /-- Perfect correctness. -/
  correct : ∀ n (m : Fin (msgLen.eval n) → Bool) (rg : gen.Coins n) (re : enc.Coins n),
    decodeFin _ (dec (pairEncode (pairSndD (gen.runAt n [] rg))
      (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re))) = some m
  /-- Ciphertexts under generated keys have `ctLen(n)` bits. -/
  enc_length : ∀ n (rg : gen.Coins n) (m : Fin (msgLen.eval n) → Bool) (re : enc.Coins n),
    (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re).length =
      ctLen.eval n

namespace FixedLengthPKScheme

/-- **The padded scheme**: a public-key scheme with ciphertexts padded to `L(n)` bits, given that
`L` bounds the honest ciphertexts (`2|c| + 2 ≤ L(n)`) and the message length (so that `⊥` on a
non-canonical `L(n)`-bit query, `|w| + 1` bits, decodes to no message). -/
noncomputable def ofPadded (msgLen : PolyExpr) (gen enc : NUPPT) (dec : List Bool → List Bool)
    (gen_uniform : gen.Uniform) (enc_uniform : enc.Uniform) (dec_poly : PolyTimeComputable dec)
    (correct : ∀ n (m : Fin (msgLen.eval n) → Bool) (rg : gen.Coins n) (re : enc.Coins n),
      decodeFin _ (dec (pairEncode (pairSndD (gen.runAt n [] rg))
        (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re))) = some m)
    (L : PolyExpr)
    (hL : ∀ n (rg : gen.Coins n) (m : Fin (msgLen.eval n) → Bool) (re : enc.Coins n),
      2 * (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re).length + 2
        ≤ L.eval n)
    (_hmsg : ∀ n, msgLen.eval n ≤ L.eval n) : FixedLengthPKScheme where
  msgLen := msgLen
  ctLen := L
  gen := gen
  enc := padEnc enc L
  dec := padDecFun dec
  gen_uniform := gen_uniform
  enc_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  dec_poly := polyTimeComputable_padDecFun dec_poly
  correct := by
    intro n m rg re
    rw [runAt_padEnc enc_uniform, padDecFun_padCt]
    exact correct n m rg (NUPPT.coinsCongr (padEnc_coins enc L) n re)
  enc_length := by
    intro n rg m re
    rw [runAt_padEnc enc_uniform]
    exact length_padCt (hL n rg m (NUPPT.coinsCongr (padEnc_coins enc L) n re))

section PaddedReaders

variable (msgLen : PolyExpr) (gen enc : NUPPT) (dec : List Bool → List Bool)
    (gen_uniform : gen.Uniform) (enc_uniform : enc.Uniform) (dec_poly : PolyTimeComputable dec)
    (correct : ∀ n (m : Fin (msgLen.eval n) → Bool) (rg : gen.Coins n) (re : enc.Coins n),
      decodeFin _ (dec (pairEncode (pairSndD (gen.runAt n [] rg))
        (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re))) = some m)
    (L : PolyExpr)
    (hL : ∀ n (rg : gen.Coins n) (m : Fin (msgLen.eval n) → Bool) (re : enc.Coins n),
      2 * (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re).length + 2
        ≤ L.eval n)
    (hmsg : ∀ n, msgLen.eval n ≤ L.eval n)

/-- The padded constructor preserves the supplied message-length polynomial. -/
theorem ofPadded_msgLen :
    (ofPadded msgLen gen enc dec gen_uniform enc_uniform dec_poly correct L hL hmsg).msgLen =
      msgLen := rfl

/-- The padded constructor's ciphertext-length polynomial is `L`. -/
theorem ofPadded_ctLen :
    (ofPadded msgLen gen enc dec gen_uniform enc_uniform dec_poly correct L hL hmsg).ctLen =
      L := rfl

/-- The padded constructor preserves the supplied key generator. -/
theorem ofPadded_gen :
    (ofPadded msgLen gen enc dec gen_uniform enc_uniform dec_poly correct L hL hmsg).gen =
      gen := rfl

/-- The padded constructor uses `padEnc enc L` as its encryptor. -/
theorem ofPadded_enc :
    (ofPadded msgLen gen enc dec gen_uniform enc_uniform dec_poly correct L hL hmsg).enc =
      padEnc enc L := rfl

/-- The padded constructor uses `padDecFun dec` as its decryptor. -/
theorem ofPadded_dec :
    (ofPadded msgLen gen enc dec gen_uniform enc_uniform dec_poly correct L hL hmsg).dec =
      padDecFun dec := rfl

end PaddedReaders

end FixedLengthPKScheme

/-- **A ch. 2–4 public-key scheme, padded** to `L(n)`-bit ciphertexts. -/
noncomputable def _root_.TCSlib.Cryptography.PublicKeyScheme.padded (S : PublicKeyScheme)
    (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (m : Fin n → Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)) re).length
        + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n) : FixedLengthPKScheme :=
  .ofPadded .var S.gen S.enc S.dec S.gen_uniform S.enc_uniform S.dec_poly
    (fun n m rg re => S.correct n m rg re) L hL hmsg

section PublicKeyPaddedReaders

variable (S : PublicKeyScheme) (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (m : Fin n → Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)) re).length
        + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n)

/-- Padding a public-key scheme preserves its message-length polynomial `PolyExpr.var`. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_msgLen :
    (S.padded L hL hmsg).msgLen = PolyExpr.var := rfl

/-- The padded public-key scheme's ciphertext-length polynomial is `L`. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_ctLen :
    (S.padded L hL hmsg).ctLen = L := rfl

/-- Padding a public-key scheme preserves its key generator. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_gen :
    (S.padded L hL hmsg).gen = S.gen := rfl

/-- The padded public-key scheme encrypts with `padEnc S.enc L`. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_enc :
    (S.padded L hL hmsg).enc = padEnc S.enc L := rfl

/-- The padded public-key scheme decrypts with `padDecFun S.dec`. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_dec :
    (S.padded L hL hmsg).dec = padDecFun S.dec := rfl

end PublicKeyPaddedReaders

/-- **A ch. 2–4 single-bit public-key scheme, padded** to `L(n)`-bit ciphertexts: one-bit
messages, `Enc` activated on `⟨pk, [b]⟩`. -/
noncomputable def _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded (S : BitPublicKeyScheme)
    (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (b : Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]) re).length + 2
        ≤ L.eval n)
    (hmsg : ∀ n, 1 ≤ L.eval n) : FixedLengthPKScheme :=
  .ofPadded (.const 1) S.gen S.enc S.dec S.gen_uniform S.enc_uniform S.dec_poly
    (fun n (m : Fin 1 → Bool) rg re => by
      have hm : List.ofFn m = [m 0] := by simp
      rw [hm, S.correct n (m 0) rg re, ← hm, decodeFin_ofFn])
    L
    (fun n rg (m : Fin 1 → Bool) re => by
      have hm : List.ofFn m = [m 0] := by simp
      rw [hm]
      exact hL n rg (m 0) re)
    hmsg

section BitPublicKeyPaddedReaders

variable (S : BitPublicKeyScheme) (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (b : Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]) re).length + 2
        ≤ L.eval n)
    (hmsg : ∀ n, 1 ≤ L.eval n)

/-- Padding a single-bit public-key scheme preserves its constant one-bit message length. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded_msgLen :
    (S.padded L hL hmsg).msgLen = PolyExpr.const 1 := rfl

/-- The padded single-bit scheme's ciphertext-length polynomial is `L`. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded_ctLen :
    (S.padded L hL hmsg).ctLen = L := rfl

/-- Padding a single-bit public-key scheme preserves its key generator. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded_gen :
    (S.padded L hL hmsg).gen = S.gen := rfl

/-- The padded single-bit scheme encrypts with `padEnc S.enc L`. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded_enc :
    (S.padded L hL hmsg).enc = padEnc S.enc L := rfl

/-- The padded single-bit scheme decrypts with `padDecFun S.dec`. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded_dec :
    (S.padded L hL hmsg).dec = padDecFun S.dec := rfl

end BitPublicKeyPaddedReaders

/-- **A padding bound exists** for every ch. 2–4 public-key scheme, from the time bounds of
`Gen` and `Enc` (`NUPPT.length_runAt_le_runLenPoly`): `|pk| ≤ Q₁(n)`, the input `⟨pk, m⟩` has at
most `2Q₁(n) + 2 + n` bits, and the ciphertext at most `Q₂(n)`; `L = 2Q₂ + 2 + n` works.

**Proof sketch.** Bound the generator's output by its running-time polynomial, which also
bounds its public-key projection. The pair-encoding length formula then bounds the encryptor's
input by `2Q₁(n) + 2 + n`. Applying the encryptor's output-length bound to this input gives
`Q₂(n)`. Choose `L(n) = 2Q₂(n) + 2 + n`: it covers the ciphertext's pair-encoding overhead and
is at least the message length `n`. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.exists_padBound (S : PublicKeyScheme) :
    ∃ L : PolyExpr,
      (∀ n (rg : S.gen.Coins n) (m : Fin n → Bool) (re : S.enc.Coins n),
        2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)) re).length
          + 2 ≤ L.eval n) ∧ ∀ n, n ≤ L.eval n := by
  have hY : ∀ n (rg : S.gen.Coins n) (m : Fin n → Bool),
      (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)).length ≤
        (PolyExpr.add (.add (.mul (.const 2) (S.gen.runLenPoly (.const 0))) (.const 2)) .var).eval
          n := by
    intro n rg m
    have h₀ := length_pairFstD_le (S.gen.runAt n [] rg)
    have h₁ := S.gen.length_runAt_le_runLenPoly (Y := .const 0) n (y := []) (by simp) rg
    simp only [length_pairEncode, List.length_ofFn, PolyExpr.eval_add, PolyExpr.eval_mul,
      PolyExpr.eval_const, PolyExpr.eval_var]
    omega
  refine ⟨.add (.add (.mul (.const 2) (S.enc.runLenPoly
    (.add (.add (.mul (.const 2) (S.gen.runLenPoly (.const 0))) (.const 2)) .var))) (.const 2))
      .var, fun n rg m re => ?_, fun n => ?_⟩
  · have h₂ := S.enc.length_runAt_le_runLenPoly n (hY n rg m) re
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    omega
  · simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    omega

/-- **A padding bound exists** for every ch. 2–4 single-bit public-key scheme (as for
`PublicKeyScheme.exists_padBound`).

**Proof sketch.** The generator's output-length bound also bounds the public key by `Q₁(n)`.
Pairing that key with one bit gives an encryptor input of at most `2Q₁(n) + 3` bits. Its
running-time bound therefore supplies a ciphertext-length polynomial `Q₂(n)`. The polynomial
`L(n) = 2Q₂(n) + 2` covers the ciphertext encoding and is at least one, as required for the
single-bit message length. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.exists_padBound (S : BitPublicKeyScheme) :
    ∃ L : PolyExpr,
      (∀ n (rg : S.gen.Coins n) (b : Bool) (re : S.enc.Coins n),
        2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]) re).length + 2
          ≤ L.eval n) ∧ ∀ n, 1 ≤ L.eval n := by
  have hY : ∀ n (rg : S.gen.Coins n) (b : Bool),
      (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]).length ≤
        (PolyExpr.add (.mul (.const 2) (S.gen.runLenPoly (.const 0))) (.const 3)).eval n := by
    intro n rg b
    have h₀ := length_pairFstD_le (S.gen.runAt n [] rg)
    have h₁ := S.gen.length_runAt_le_runLenPoly (Y := .const 0) n (y := []) (by simp) rg
    simp only [length_pairEncode, List.length_singleton, PolyExpr.eval_add, PolyExpr.eval_mul,
      PolyExpr.eval_const]
    omega
  refine ⟨.add (.mul (.const 2) (S.enc.runLenPoly
    (.add (.mul (.const 2) (S.gen.runLenPoly (.const 0))) (.const 3)))) (.const 2),
      fun n rg b re => ?_, fun n => ?_⟩
  · have h₂ := S.enc.length_runAt_le_runLenPoly n (hY n rg b) re
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega
  · simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega

/-! ### The experiment of Definition 171.5 -/

namespace FixedLengthPKScheme

variable (S : FixedLengthPKScheme)

/-- The query lengths of the two oracles `Dec` and `Challenge` at parameter `n`. -/
def inLens (n : ℕ) : Fin 2 → ℕ
  | 0 => S.ctLen.eval n
  | 1 => S.msgLen.eval n + S.msgLen.eval n

/-- Decryption queries have the scheme's ciphertext length. -/
theorem inLens_zero (n : ℕ) : S.inLens n 0 = S.ctLen.eval n := rfl

/-- Challenge queries contain two messages of the scheme's message length. -/
theorem inLens_one (n : ℕ) : S.inLens n 1 = S.msgLen.eval n + S.msgLen.eval n := rfl

/-- The answer lengths: `Dec` answers a validity flag and a message; `Challenge` a ciphertext. -/
def outLens (n : ℕ) : Fin 2 → ℕ
  | 0 => S.msgLen.eval n + 1
  | 1 => S.ctLen.eval n

/-- Decryption answers contain a validity bit followed by one message. -/
theorem outLens_zero (n : ℕ) : S.outLens n 0 = S.msgLen.eval n + 1 := rfl

/-- Challenge answers have the scheme's ciphertext length. -/
theorem outLens_one (n : ℕ) : S.outLens n 1 = S.ctLen.eval n := rfl

/-- The two oracles of the experiment at parameter `n`. -/
abbrev indSpec (n : ℕ) : OracleSpec (Fin 2) := bitSpec (S.inLens n) (S.outLens n)

/-- The public-key IND oracle specification is the bit specification at the scheme's query
and answer lengths. -/
theorem indSpec_eq (n : ℕ) : S.indSpec n = bitSpec (S.inLens n) (S.outLens n) := rfl

/-- Oracle `i` accepts bit strings of length `S.inLens n i`. -/
theorem indSpec_dom (n : ℕ) (i : Fin 2) :
    (S.indSpec n).dom i = (Fin (S.inLens n i) → Bool) :=
  bitSpec_dom (S.inLens n) (S.outLens n) i

/-- The decryption oracle accepts a ciphertext at the scheme's encoded width. -/
theorem indSpec_decDom (n : ℕ) : (S.indSpec n).dom 0 = (Fin (S.ctLen.eval n) → Bool) := by
  rw [S.indSpec_dom, S.inLens_zero]

/-- Oracle `i` returns bit strings of length `S.outLens n i`. -/
theorem indSpec_rng (n : ℕ) (i : Fin 2) :
    (S.indSpec n).rng i = (Fin (S.outLens n i) → Bool) :=
  bitSpec_rng (S.inLens n) (S.outLens n) i

/-- **The oracles of `Ind_b`** at parameter `n`, for the keys `pk`, `sk`; the state is the
challenge, once asked.
- `Dec` answers `⟨1, Dec_sk(c)⟩` when it is open (`decOpen`) and `c` is not the challenge, and
  `⊥` (all `false`) otherwise; an output that decodes to no message is `⊥` as well.
- `Challenge` answers `Enc_pk(m_b)` on `⟨m₀, m₁⟩` the first time it is asked, and records it;
  later it repeats the recorded challenge. -/
noncomputable def indImpl (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool) :
    QueryImpl (S.indSpec n) (Option (Fin (S.ctLen.eval n) → Bool)) unifSpec
  | 0, c, s =>
    if FixedLengthScheme.decOpen atk s.isSome && !decide (s = some c) then
      .pure (FixedLengthScheme.decAnswer (decodeFin _ (S.dec (pairEncode sk (List.ofFn c)))), s)
    else .pure (zeroBits _, s)
  | 1, mm, s =>
    match s with
    | some c => .pure (c, s)
    | none =>
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let c := padFin _ (S.enc.runAt n (pairEncode pk (List.ofFn
          (if b then (FixedLengthScheme.splitHalf mm).2 else (FixedLengthScheme.splitHalf mm).1)))
          r)
        .pure (c, some c)

/-- A decryption query checks oracle availability and refuses the recorded challenge;
otherwise it returns the decoded plaintext with its validity flag, preserving the state. -/
theorem indImpl_dec (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (c : Fin (S.ctLen.eval n) → Bool) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl atk b n pk sk 0 c s =
      if FixedLengthScheme.decOpen atk s.isSome && !decide (s = some c) then
        .pure (FixedLengthScheme.decAnswer
          (decodeFin _ (S.dec (pairEncode sk (List.ofFn c)))), s)
      else .pure (zeroBits _, s) := rfl

/-- The first challenge query encrypts the selected message half using fresh coins and
records the padded ciphertext. -/
theorem indImpl_challenge_none (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (mm : Fin (S.msgLen.eval n + S.msgLen.eval n) → Bool) :
    S.indImpl atk b n pk sk 1 mm none =
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let c := padFin (S.ctLen.eval n) (S.enc.runAt n (pairEncode pk (List.ofFn
          (if b then (FixedLengthScheme.splitHalf mm).2 else (FixedLengthScheme.splitHalf mm).1)))
          r)
        .pure (c, some c) := rfl

/-- A repeated challenge query returns the recorded ciphertext and preserves it as state. -/
theorem indImpl_challenge_repeat (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (mm : Fin (S.msgLen.eval n + S.msgLen.eval n) → Bool) (c : Fin (S.ctLen.eval n) → Bool) :
    S.indImpl atk b n pk sk 1 mm (some c) = .pure (c, some c) := rfl

/-- The decryption equation on the query specification's type. Read the ciphertext through
the width equality before checking challenge refusal and decrypting. -/
theorem indImpl_dec_onSpec (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (c : (S.indSpec n).dom 0) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl atk b n pk sk 0 c s =
      if FixedLengthScheme.decOpen atk s.isSome && !decide (s = some (cast (S.indSpec_decDom n) c))
      then .pure (FixedLengthScheme.decAnswer
        (decodeFin _ (S.dec (pairEncode sk (List.ofFn (cast (S.indSpec_decDom n) c))))), s)
      else .pure (zeroBits _, s) := by
  simpa only [cast_eq] using S.indImpl_dec atk b n pk sk c s

/-- The challenge oracle returns a ciphertext at the scheme's encoded width. -/
theorem indSpec_challengeRng (n : ℕ) :
    (S.indSpec n).rng 1 = (Fin (S.ctLen.eval n) → Bool) := by
  rw [S.indSpec_rng, S.outLens_one]

/-- A challenge query contains two messages at the scheme's message width. -/
theorem indSpec_challengeDom (n : ℕ) :
    (S.indSpec n).dom 1 = (Fin (S.msgLen.eval n + S.msgLen.eval n) → Bool) := by
  rw [S.indSpec_dom, S.inLens_one]

/-- The fresh challenge equation on the query specification's type. Draw new encryption
coins, encrypt the selected half of the query, and record the resulting ciphertext. -/
theorem indImpl_challenge_none_onSpec (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (mm : (S.indSpec n).dom 1) :
    S.indImpl atk b n pk sk 1 mm none =
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let halves := FixedLengthScheme.splitHalf (cast (S.indSpec_challengeDom n) mm)
        let c := padFin (S.ctLen.eval n) (S.enc.runAt n
          (pairEncode pk (List.ofFn (if b then halves.2 else halves.1))) r)
        .pure (cast (S.indSpec_challengeRng n).symm c, some c) := by
  simpa only [cast_eq] using S.indImpl_challenge_none atk b n pk sk mm

/-- Repeating the challenge preserves the previous state for a query of the specification's
type. -/
theorem indImpl_challenge_repeat_onSpec (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (mm : (S.indSpec n).dom 1) (c : Fin (S.ctLen.eval n) → Bool) :
    S.indImpl atk b n pk sk 1 mm (some c) = .pure (cast (S.indSpec_challengeRng n).symm c, some c) := by
  simpa only [cast_eq] using S.indImpl_challenge_repeat atk b n pk sk mm c

/-- Under CPA, `Dec` never answers. -/
theorem indImpl_dec_cpa (b : Bool) (n : ℕ) (pk sk : List Bool)
    (c : Fin (S.ctLen.eval n) → Bool) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl .cpa b n pk sk 0 c s = .pure (zeroBits _, s) := by
  simp [indImpl, FixedLengthScheme.decOpen_cpa]

/-- Under CCA2, `Dec` refuses the challenge. -/
theorem indImpl_dec_cca2_challenge (b : Bool) (n : ℕ) (pk sk : List Bool)
    (c : Fin (S.ctLen.eval n) → Bool) :
    S.indImpl .cca2 b n pk sk 0 c (some c) = .pure (zeroBits _, some c) := by
  simp [indImpl, FixedLengthScheme.decOpen_cca2]

/-- The codec of the adversary: the two oracles, and a one-bit final output. -/
def indCodec (n : ℕ) : MachineCodec (S.indSpec n) (Fin 1 → Bool) :=
  bitCodec (S.inLens n) (S.outLens n) 1

/-- The public-key IND codec decodes a move with the bit decoder at the scheme's oracle
lengths and a one-bit final output. -/
theorem indCodec_decodeMove (n : ℕ) (w : List Bool) :
    (S.indCodec n).decodeMove w = decodeBitMove (S.inLens n) (S.outLens n) 1 w :=
  bitCodec_decodeMove (S.inLens n) (S.outLens n) 1 w

/-- The public-key IND codec encodes an entry by pairing the unary oracle index with its
query and answer strings. -/
theorem indCodec_encodeEntry (n : ℕ)
    (e : Σ i, (S.indSpec n).dom i × (S.indSpec n).rng i) :
    (S.indCodec n).encodeEntry e =
      pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)) :=
  bitCodec_encodeEntry (S.inLens n) (S.outLens n) 1 e

/-- The public-key IND codec returns the false one-bit result on timeout. -/
theorem indCodec_timeout (n : ℕ) : (S.indCodec n).timeout = zeroBits 1 :=
  bitCodec_timeout (S.inLens n) (S.outLens n) 1

/-- **The experiment `Ind_b(Π, A, n)`** [PS10, Definition 171.5] for the attack `atk`, with query
budget `q`: sample `(pk, sk) ← Gen(1^n)` and `A`'s coins, run `A` on `pk` against the oracles
from the unchallenged state, and output its bit. -/
noncomputable def indGame (atk : Attack) (A : NUPPT) (q : ℕ) (b : Bool) (n : ℕ) : ProbComp Bool :=
  (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (A.Coins n)).bind fun r =>
  (simulate (S.indImpl atk b n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg)))
      (A.toCompOn (S.indCodec n) n q (pairFstD (S.gen.runAt n [] rg)) r) none).bind
    fun res => .pure (res.1 0)

/-- The public-key IND game samples key-generation and adversary coins, simulates the
oracles on the public-key input from the unchallenged state, and returns the final bit. -/
theorem indGame_eq (atk : Attack) (A : NUPPT) (q : ℕ) (b : Bool) (n : ℕ) :
    S.indGame atk A q b n =
      (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
      (ProbComp.sample (A.Coins n)).bind fun r =>
      (simulate (S.indImpl atk b n (pairFstD (S.gen.runAt n [] rg))
          (pairSndD (S.gen.runAt n [] rg)))
        (A.toCompOn (S.indCodec n) n q (pairFstD (S.gen.runAt n [] rg)) r) none).bind
        fun res => .pure (res.1 0) := rfl

/-- **CPA, CCA1 or CCA2 security of a public-key scheme** [PS10, Definition 171.5]: for every
non-uniform PPT `A` and every polynomial query budget, `A`'s advantage between `Ind_0` and
`Ind_1` is negligible. -/
def INDSecure (atk : Attack) : Prop :=
  ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n, advantage (S.indGame atk A (q.eval n) false n) (S.indGame atk A (q.eval n) true n) ≤ ε n

/-- Public-key IND security is exactly negligible advantage for every non-uniform PPT
adversary and polynomial query budget, uniformly over the security parameter. -/
theorem INDSecure_iff (atk : Attack) :
    S.INDSecure atk ↔ ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n, advantage (S.indGame atk A (q.eval n) false n)
        (S.indGame atk A (q.eval n) true n) ≤ ε n := Iff.rfl

end FixedLengthPKScheme

/-! ### From ensemble security to CPA -/

section PaddedCPA

open ChallengeSim ProbComp

/-- The reduction's challenge answer, read from its context `⟨1^n, ⟨⟨pk, c⟩, ω⟩⟩`: the padding
`padCt L(n) c` of the ciphertext it received. -/
private def cpaAns (L : PolyExpr) (ctx : List Bool) : List Bool :=
  padCt (L.eval (pairFstD ctx).length) (pairSndD (pairFstD (pairSndD ctx)))

/-- The challenge answer is polynomial-time (as `padEncFun`). -/
private theorem polyTimeComputable_cpaAns (L : PolyExpr) : PolyTimeComputable (cpaAns L) := by
  have hc : PolyTimeComputable fun ctx => pairSndD (pairFstD (pairSndD ctx)) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
  have h := hc.pairEncode ((polyTimeComputable_pairDropPoly .var).comp
    ((hc.pairEncode (polyTimeComputable_const [])).pairEncode
      ((polyTimeComputable_unaryPoly L).comp polyTimeComputable_pairFstD)))
  convert h using 1
  funext ctx
  simp [cpaAns, padCt_eq, Function.comp_apply, length_pairEncode]

/-- On the context `⟨1^n, ⟨z, ω⟩⟩` the challenge answer is `padCt L(n) (pairSndD z)`. -/
private theorem cpaAns_seedIn (L : PolyExpr) (n : ℕ) (z ω : List Bool) :
    cpaAns L (seedIn n z ω) = padCt (L.eval n) (pairSndD z) := by
  simp only [cpaAns, seedIn_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]

/-- The selected half of a two-bit challenge query, as a list, is its bit `0` or `1`. -/
private theorem ofFn_splitHalf_bit {k : ℕ} (hk : k = 1) (b : Bool) (mm : Fin (k + k) → Bool) :
    List.ofFn (if b then (FixedLengthScheme.splitHalf mm).2
      else (FixedLengthScheme.splitHalf mm).1) =
      [(List.ofFn mm).getD (if b then 1 else 0) false] := by
  subst hk
  cases b <;> simp [FixedLengthScheme.splitHalf_fst, FixedLengthScheme.splitHalf_snd,
    List.ofFn_succ]

/-- **Eager challenge coins** (checkpoint 1). Under CPA, simulating the oracles of `Ind_b` from
the state `s` has, for every function `G` of the output, the expectation of first sampling the
encryption coins `re` and then running the deterministic oracles whose challenge answer is the
encryption of `m_b` with coins `re` (`chRun`).

**Proof sketch.** Induction on the computation. Decryption queries are answered all-`false`
in both (`indImpl_dec_cpa`); a repeated challenge repeats the recorded ciphertext in both. At the
first challenge the lazy side samples `re` and continues from the recorded ciphertext; by the
induction hypothesis the continuation is again an average over coins `re'`, and from a recorded
state the deterministic run does not depend on `re'` (`chRun_some_congr`), so `re'`
marginalizes out (`expect_const`). -/
private theorem expect_simulate_indImpl_cpa (S : FixedLengthPKScheme) (b : Bool) (n : ℕ)
    (pk sk : List Bool) {α : Type} (G : α → ℝ) (c : OracleComp (S.indSpec n) α)
    (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    expect (simulate (S.indImpl .cpa b n pk sk) c s) (fun p => G p.1) =
      expect (ProbComp.sample (S.enc.Coins n)) fun re =>
        G (chRun (fun mm => S.enc.runAt n (pairEncode pk (List.ofFn
          (if b then (FixedLengthScheme.splitHalf mm).2
            else (FixedLengthScheme.splitHalf mm).1))) re) c s).1 := by
  induction c generalizing s with
  | pure a =>
    rw [simulate_pure, expect_pure]
    simp only [chRun_pure]
    exact (expect_const _ _).symm
  | query i x k ih =>
    match i, x, k, ih with
    | 0, x, k, ih =>
      rw [simulate_query, S.indImpl_dec_cpa, OracleComp.pure_bind]
      simp only [chRun_query_zero]
      exact ih _ s
    | 1, x, k, ih =>
      cases s with
      | some C =>
        rw [simulate_query, S.indImpl_challenge_repeat, OracleComp.pure_bind]
        simp only [chRun_query_one_some]
        exact ih _ _
      | none =>
        rw [simulate_query, S.indImpl_challenge_none, OracleComp.bind_assoc, expect_bind]
        refine congrArg _ (funext fun re => ?_)
        rw [OracleComp.pure_bind, ih, chRun_query_one_none]
        exact (congrArg _ (funext fun re' =>
          congrArg (fun p : α × Option (Fin (S.ctLen.eval n) → Bool) => G p.1)
            (chRun_some_congr _ _ _ _))).trans (expect_const _ _)

/-- **The exact identity of step 4.** Let `B` be the machine of T1 for the recording handler
with challenge answer `cpaAns L` (with its coin bijection `φ`). At every `n`, `A`'s CPA advantage
against the padded scheme equals `B`'s advantage between `⟨pk, Enc_pk(0)⟩` and `⟨pk, Enc_pk(1)⟩`.

**Proof sketch.** Fix `n`. Game `b` samples `rg`, `A`'s coins `r` and (eagerly,
`expect_simulate_indImpl_cpa`) encryption coins `re`; by first-challenge congruence (`chRun_congr`)
its output is `A`'s bit `F(w)` when the challenge is answered with `w = padCt L(n) (Enc(m_b; re))`,
where `(m₀, m₁)` is `A`'s first challenge query (`firstQ`), or `F` of anything without one. On
`z = ⟨pk, Enc(β; re)⟩`, T1 and `simulate_recHandler_init` show that `B` with coins `φ (ω, r)` runs
`A` with the same answers `padCt L(n) (Enc(β; re))` and outputs the post-processed bit
(`recOut_init`, `recOut_recorded`), after transporting the run between the two equal codecs
(`chRun_toCompOn_transport`). Rearranging the samples (`expect_sample_prod`, `_comm`, `_equiv`
along `φ` and `padEnc_coins`, `_unique` for the empty seed), both differences of acceptance
rates become `𝔼_{rg, r}` of a pointwise difference, which agree by `expect_indicator_sub`. -/
private theorem padded_cpa_advantage_eq {S : BitPublicKeyScheme} (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (b : Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]) re).length + 2
        ≤ L.eval n)
    (hmsg : ∀ n, 1 ≤ L.eval n) (A : NUPPT) (q : PolyExpr) (B : NUPPT) (n : ℕ)
    (φ : (Fin ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).seedLen.eval n) → Bool) ×
      A.Coins n ≃ B.Coins n)
    (hφ : ∀ (z : List Bool)
      (ω : Fin ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).seedLen.eval n) → Bool)
      (r : A.Coins n),
      ∃ (a : Fin ((PolyExpr.const 1).eval n) → Bool)
        (s : Fin ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).stateLen.eval n) → Bool),
        simulate ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).impl n z ω)
            (A.toCompOn (bitCodec (fun i => (recDin L i).eval n) (fun i => (recDout L i).eval n)
              ((PolyExpr.const 1).eval n)) n (q.eval n)
              ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).advInput n z ω) r)
            ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).init n) = .pure (a, s) ∧
          B.runAt n z (φ (ω, r)) =
            (recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).result n z ω s a) :
    advantage ((S.padded L hL hmsg).indGame .cpa A (q.eval n) false n)
        ((S.padded L hL hmsg).indGame .cpa A (q.eval n) true n) =
      distAdv (S.pkEncDist n false) (S.pkEncDist n true) (B.distinguisherL n) := by
  -- Notation: the game's computation, the padded ciphertexts, and `A`'s bit.
  set S' := S.padded L hL hmsg with hS'
  let comp : S.gen.Coins n → A.Coins n → OracleComp (S'.indSpec n) (Fin 1 → Bool) :=
    fun rg r => A.toCompOn (S'.indCodec n) n (q.eval n) (pairFstD (S.gen.runAt n [] rg)) r
  let W : Bool → S.gen.Coins n → S.enc.Coins n → List Bool := fun β rg re =>
    padCt (L.eval n) (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [β]) re)
  let F : S.gen.Coins n → A.Coins n → List Bool → Bool := fun rg r w =>
    (chRun (fun _ => w) (comp rg r) none).1 0
  -- The two codecs have equal lengths.
  have hins : (fun i => (recDin L i).eval n) = S'.inLens n := by
    funext i
    match i with
    | 0 => rw [recDin_zero, FixedLengthPKScheme.inLens_zero, BitPublicKeyScheme.padded_ctLen]
    | 1 =>
      rw [recDin_one, FixedLengthPKScheme.inLens_one, BitPublicKeyScheme.padded_msgLen,
        PolyExpr.eval_const, PolyExpr.eval_const]
  have houts : (fun i => (recDout L i).eval n) = S'.outLens n := by
    funext i
    match i with
    | 0 =>
      rw [recDout_zero, FixedLengthPKScheme.outLens_zero, BitPublicKeyScheme.padded_msgLen,
        PolyExpr.eval_const, PolyExpr.eval_const]
    | 1 => rw [recDout_one, FixedLengthPKScheme.outLens_one, BitPublicKeyScheme.padded_ctLen]
  -- Step 4, game side: eager coins, first-challenge congruence, and the coin transport.
  have hG : ∀ b : Bool, accept (S'.indGame .cpa A (q.eval n) b n) =
      expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
        expect (ProbComp.sample (A.Coins n)) fun r =>
          expect (ProbComp.sample (S.enc.Coins n)) fun re =>
            if F rg r ((firstQ (comp rg r)).elim []
                fun l => W (l.getD (if b then 1 else 0) false) rg re) = true then 1 else 0 := by
    intro b
    rw [accept_eq, FixedLengthPKScheme.indGame_eq, prob_bind]
    refine congrArg _ (funext fun rg => ?_)
    rw [prob_bind]
    refine congrArg _ (funext fun r => ?_)
    rw [prob_bind]
    refine (expect_simulate_indImpl_cpa S' b n _ _
      (fun a => ProbComp.prob (.pure (a 0)) (· = true)) (comp rg r) none).trans ?_
    rw [← expect_sample_equiv (NUPPT.coinsCongr (padEnc_coins S.enc L) n)]
    refine congrArg _ (funext fun re' => ?_)
    rw [prob_pure]
    congr 2
    refine congrArg (fun p : (Fin 1 → Bool) × Option (Fin (S'.ctLen.eval n) → Bool) => p.1 0)
      (chRun_congr _ _ _ fun mm hmm => ?_)
    rw [hmm, Option.elim_some]
    exact (runAt_padEnc S.enc_uniform L n _ re').trans (by
      rw [ofFn_splitHalf_bit (by rw [BitPublicKeyScheme.padded_msgLen, PolyExpr.eval_const])]
      rfl)
  -- Step 4, distinguisher side: T1, the handler's simulation, and the codec transport.
  have hpt : ∀ (β : Bool) (rg : S.gen.Coins n) (r : A.Coins n) (re : S.enc.Coins n)
      (ω : Fin ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).seedLen.eval n) → Bool),
      B.distinguisherL n (S.pkEncDist n β (rg, re)) (φ (ω, r)) =
        (firstQ (comp rg r)).elim false fun l =>
          (l.getD 0 false != l.getD 1 false) && (F rg r (W β rg re) != l.getD 0 false) := by
    intro β rg r re ω
    obtain ⟨a, s, hsim, hrun⟩ := hφ (S.pkEncDist n β (rg, re)) ω r
    have hadv :
        (recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).advInput n
          (S.pkEncDist n β (rg, re)) ω =
        pairFstD (S.gen.runAt n [] rg) := by
      rw [PolyHandler.advInput_eq, recHandler_advIn, recAdvIn_eq, seedIn_eq,
        BitPublicKeyScheme.pkEncDist_eq, pairSndD_pairEncode, pairFstD_pairEncode,
        pairFstD_pairEncode]
    have hans : cpaAns L (seedIn n (S.pkEncDist n β (rg, re)) (List.ofFn ω)) = W β rg re := by
      rw [cpaAns_seedIn, BitPublicKeyScheme.pkEncDist_eq, pairSndD_pairEncode]
    have hw : (cpaAns L (seedIn n (S.pkEncDist n β (rg, re)) (List.ofFn ω))).length =
        L.eval n := by
      rw [hans]
      exact length_padCt (hL n rg β re)
    obtain ⟨s', hsim', hs'⟩ := simulate_recHandler_init L (polyTimeComputable_cpaAns L) n
      (S.pkEncDist n β (rg, re)) ω hw _
    rw [hsim, OracleComp.pure.injEq, Prod.mk.injEq] at hsim'
    obtain ⟨rfl, rfl⟩ := hsim'
    obtain ⟨h₁, h₂⟩ := chRun_toCompOn_transport hins houts (PolyExpr.eval_const 1 n)
      A n (q.eval n) ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).advInput n
        (S.pkEncDist n β (rg, re)) ω) r (W β rg re)
    rw [hadv] at h₁ h₂ hs'
    rw [h₂] at hs'
    rw [NUPPT.distinguisherL_eq, hrun, PolyHandler.result_eq, recHandler_out]
    have ha : List.ofFn (chRun (fun _ => cpaAns L (seedIn n (S.pkEncDist n β (rg, re))
        (List.ofFn ω))) (A.toCompOn (bitCodec (fun i => (recDin L i).eval n)
          (fun i => (recDout L i).eval n) ((PolyExpr.const 1).eval n)) n (q.eval n)
            ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).advInput n
              (S.pkEncDist n β (rg, re)) ω) r) none).1 =
        [F rg r (W β rg re)] := by
      rw [hans, hadv, h₁, List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [ha]
    cases hq : firstQ (comp rg r) with
    | none =>
      have hq' : firstQ (A.toCompOn (bitCodec (S'.inLens n) (S'.outLens n) 1) n (q.eval n)
          (pairFstD (S.gen.runAt n [] rg)) r) = none := hq
      rw [hq', Option.elim_none] at hs'
      rw [hs', recOut_init, Option.elim_none]
      decide
    | some l =>
      have hq' : firstQ (A.toCompOn (bitCodec (S'.inLens n) (S'.outLens n) 1) n (q.eval n)
          (pairFstD (S.gen.runAt n [] rg)) r) = some l := hq
      have hl : l.length = 2 := by
        rw [length_of_firstQ_eq_some _ hq', FixedLengthPKScheme.inLens_one,
          BitPublicKeyScheme.padded_msgLen, PolyExpr.eval_const]
      obtain ⟨m₀, m₁, rfl⟩ := List.length_eq_two.1 hl
      rw [hq', Option.elim_some] at hs'
      rw [hs', recOut_recorded, Option.elim_some]
      simp only [List.headD_cons, List.getD_cons_zero, List.getD_cons_succ, List.cons.injEq,
        and_true, Bool.decide_eq_true]
  have hD : ∀ β : Bool, acceptProb (S.pkEncDist n β) (B.distinguisherL n) =
      expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
        expect (ProbComp.sample (A.Coins n)) fun r =>
          expect (ProbComp.sample (S.enc.Coins n)) fun re =>
            if ((firstQ (comp rg r)).elim false fun l =>
              (l.getD 0 false != l.getD 1 false) && (F rg r (W β rg re) != l.getD 0 false)) = true
            then 1 else 0 := by
    intro β
    rw [Bridge.acceptProb_eq, accept_eq, Bridge.acceptGame_eq, prob_bind, expect_sample_prod]
    refine congrArg _ (funext fun rg => ?_)
    simp only [prob_bind, prob_pure]
    haveI : Unique (Fin ((recHandler L (cpaAns L) (polyTimeComputable_cpaAns L)).seedLen.eval n) →
        Bool) := by
      rw [recHandler_seedLen, PolyExpr.eval_const]
      infer_instance
    rw [expect_sample_comm, ← expect_sample_equiv φ, expect_sample_prod, expect_sample_unique]
    refine congrArg _ (funext fun r => congrArg _ (funext fun re => ?_))
    rw [hpt β rg r re]
  -- Assemble: both differences are `𝔼_{rg, r}` of equal pointwise differences.
  rw [advantage_eq, distAdv_def, hG false, hG true, hD false, hD true]
  congr 1
  rw [← expect_sub]
  conv_rhs => rw [← expect_sub]
  refine congrArg _ (funext fun rg => ?_)
  rw [← expect_sub]
  conv_rhs => rw [← expect_sub]
  refine congrArg _ (funext fun r => ?_)
  cases hq : firstQ (comp rg r) with
  | none =>
    simp only [Option.elim_none, Bool.false_eq_true, if_false, sub_self]
  | some l =>
    have hl : l.length = 2 := by
      rw [length_of_firstQ_eq_some _ hq, FixedLengthPKScheme.inLens_one,
        BitPublicKeyScheme.padded_msgLen, PolyExpr.eval_const]
    obtain ⟨m₀, m₁, rfl⟩ := List.length_eq_two.1 hl
    simp only [Option.elim_some, List.getD_cons_zero, List.getD_cons_succ, Bool.false_eq_true,
      if_false, if_true]
    exact expect_indicator_sub (fun β re => F rg r (W β rg re)) m₀ m₁

/-- **Single-bit security gives CPA security** for a padded single-bit scheme.

**Proof sketch.**
1. With CPA there is no `Dec` oracle, so the adversary's view is `pk`, its coins and the padded
   challenge `padCt L (Enc_pk(m_b))`, where its messages `m₀, m₁ ∈ {0,1}` are chosen after
   seeing `pk`. Only the first challenge query uses coins, so the encryption coins may be sampled
   in advance (`expect_simulate_indImpl_cpa`); then `A`'s bit depends on the challenge answer only
   through its value at `A`'s first challenge query `(m₀, m₁)`, which itself does not depend on
   that answer (`ChallengeSim.chRun_congr`).
2. If `m₀ = m₁` both games are identical. Otherwise `m_b` is `b` or `¬b`. The distinguisher `D`
   on `⟨pk, c⟩` runs `A` on `pk`, answers every challenge with `padCt L c` and every `Dec` query
   with `⊥`, records `A`'s first challenge `(m₀, m₁)`, and outputs `A`'s bit, flipped when
   `(m₀, m₁) = (1, 0)` and replaced by `0` when `m₀ = m₁` or no challenge was asked. T1
   (`Games.exists_handlerMachine`, for the handler `ChallengeSim.recHandler`) makes `D` a
   machine, whose output is exactly this bit (`ChallengeSim.simulate_recHandler_init`).
3. Fixing `pk` and `A`'s coins, the case split on `(m₀, m₁)` gives the same difference of
   acceptance rates on both sides (`ChallengeSim.expect_indicator_sub`); so `A`'s CPA advantage
   equals `D`'s advantage between `⟨pk, Enc_pk(0)⟩` and `⟨pk, Enc_pk(1)⟩` at every `n`
   (`padded_cpa_advantage_eq`), which is negligible (`BitPublicKeyScheme.singleBitSecure_iff`). -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.padded_cpa
    {S : BitPublicKeyScheme} (h : S.SingleBitSecure) (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (b : Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]) re).length + 2
        ≤ L.eval n)
    (hmsg : ∀ n, 1 ≤ L.eval n) : (S.padded L hL hmsg).INDSecure .cpa := by
  rw [FixedLengthPKScheme.INDSecure_iff]
  intro A q
  -- Step 3: the distinguisher `D` is T1's machine for the recording handler.
  obtain ⟨B, hB⟩ := exists_handlerMachine A q (recDin L) (recDout L) (.const 1)
    (recHandler L (cpaAns L) (polyTimeComputable_cpaAns L))
  refine ⟨_, (BitPublicKeyScheme.singleBitSecure_iff S).1 h B, fun n => le_of_eq ?_⟩
  -- Step 4: the advantages are equal.
  obtain ⟨φ, hφ⟩ := hB n
  exact padded_cpa_advantage_eq L hL hmsg A q B n φ hφ

end PaddedCPA

end TCSlib.Cryptography.Composability

## ===== TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/ChallengeSim.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Cryptography.Games.Machines
import TCSlib.Cryptography.Games.Probability
import TCSlib.Cryptography.Games.Bridges.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A deterministic challenge oracle under CPA

Under a chosen-plaintext attack the IND experiment of [PS10, Definition 171.5] has two oracles
in the encoding of `Encryption.PublicKey.OracleSecurity`: a decryption oracle that always
answers all-`false`, and a challenge oracle that answers the first query `⟨m₀, m₁⟩` with a
ciphertext and repeats it afterwards. This file studies that pair of oracles on bit strings of
arbitrary lengths (`bitSpec ins outs`) when the first challenge answer is a deterministic
function `g` of the query, for example once the encryption coins have been sampled in advance.

The run is a pure function of the computation (`chRun`). Its result depends on `g` only through
`g` at the first challenge query (`firstQ`), which does not depend on `g` at all
(`chRun_congr`). This replaces the informal "condition on the adversary's choice of messages"
in the proof of the claim after Definition 171.5. Both the run and the first query transport
along equalities of the length functions (`chRun_toCompOn_transport`), which aligns two codecs
with propositionally equal lengths.

The last section collects sampling identities used to rearrange the expectations of the CPA
reduction: reindexing by an equivalence, products, exchange of order, and singleton types.

## Main definitions

* `Composability.ChallengeSim.chRun g c s`: the run of `c` against the CPA oracles with the
  deterministic challenge answer `g`, from the challenge state `s`.
* `Composability.ChallengeSim.firstQ c`: the first challenge query of `c`, as a list.

## Main results

* `ChallengeSim.chRun_some_congr`: once the challenge is recorded, `g` no longer matters.
* `ChallengeSim.chRun_congr`: the run depends on `g` only at the first challenge query.
* `ChallengeSim.length_of_firstQ_eq_some`: the first challenge query has `ins 1` bits.
* `ChallengeSim.chRun_toCompOn_transport`: transport along equal length functions.
* `ChallengeSim.expect_sample_equiv`, `expect_sample_prod`, `expect_sample_comm`,
  `expect_sample_unique`, `expect_sub`: sampling identities.
* `ChallengeSim.expect_indicator_sub`: the case split on the first challenge `(m₀, m₁)`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.1.4, Definition 171.5 and the claim after it (book pp. 171–172).
-/

namespace TCSlib.Cryptography.Composability.ChallengeSim

open Complexity TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

variable {ins outs : Fin 2 → ℕ} {α : Type}

/-! ### The deterministic run -/

/-- **The run of `c` against the CPA oracles with the challenge answer `g`**, from the challenge
state `s`: oracle `0` answers all-`false` and keeps the state; oracle `1` answers the first query
`mm` with `padFin (outs 1) (g mm)` and records it, and later repeats the recorded answer. The
result is `c`'s output and the final state. -/
def chRun (g : (Fin (ins 1) → Bool) → List Bool) :
    OracleComp (bitSpec ins outs) α → Option (Fin (outs 1) → Bool) →
      α × Option (Fin (outs 1) → Bool)
  | .pure a, s => (a, s)
  | .query 0 _ k, s => chRun g (k (zeroBits _)) s
  | .query 1 mm k, none => chRun g (k (padFin _ (g mm))) (some (padFin _ (g mm)))
  | .query 1 _ k, some c => chRun g (k c) (some c)

/-- A return ends the run: `chRun g (pure a) s = (a, s)`. -/
theorem chRun_pure (g : (Fin (ins 1) → Bool) → List Bool) (a : α)
    (s : Option (Fin (outs 1) → Bool)) : chRun g (.pure a) s = (a, s) := rfl

/-- A query to oracle `0` is answered all-`false`, keeping the state:
`chRun g (query 0 x k) s = chRun g (k 0) s`. -/
theorem chRun_query_zero (g : (Fin (ins 1) → Bool) → List Bool) (x : Fin (ins 0) → Bool)
    (k : (Fin (outs 0) → Bool) → OracleComp (bitSpec ins outs) α)
    (s : Option (Fin (outs 1) → Bool)) :
    chRun g (.query 0 x k) s = chRun g (k (zeroBits _)) s := rfl

/-- The first challenge query `mm` is answered with `padFin (outs 1) (g mm)`, which is recorded. -/
theorem chRun_query_one_none (g : (Fin (ins 1) → Bool) → List Bool) (mm : Fin (ins 1) → Bool)
    (k : (Fin (outs 1) → Bool) → OracleComp (bitSpec ins outs) α) :
    chRun g (.query 1 mm k) none = chRun g (k (padFin _ (g mm))) (some (padFin _ (g mm))) := rfl

/-- A later challenge query repeats the recorded answer `c`. -/
theorem chRun_query_one_some (g : (Fin (ins 1) → Bool) → List Bool) (mm : Fin (ins 1) → Bool)
    (k : (Fin (outs 1) → Bool) → OracleComp (bitSpec ins outs) α) (c : Fin (outs 1) → Bool) :
    chRun g (.query 1 mm k) (some c) = chRun g (k c) (some c) := rfl

/-- **The first challenge query** of `c` against the CPA oracles, as a list: queries to oracle `0`
are answered all-`false` and skipped; the first query `mm` to oracle `1` gives `List.ofFn mm`; a
computation that returns before it gives `none`. -/
def firstQ : OracleComp (bitSpec ins outs) α → Option (List Bool)
  | .pure _ => none
  | .query 0 _ k => firstQ (k (zeroBits _))
  | .query 1 mm _ => some (List.ofFn mm)

/-- A return asks no challenge: `firstQ (pure a) = none`. -/
theorem firstQ_pure (a : α) : firstQ (ins := ins) (outs := outs) (.pure a) = none := rfl

/-- A query to oracle `0` is skipped: `firstQ (query 0 x k) = firstQ (k 0)`. -/
theorem firstQ_query_zero (x : Fin (ins 0) → Bool)
    (k : (Fin (outs 0) → Bool) → OracleComp (bitSpec ins outs) α) :
    firstQ (.query 0 x k) = firstQ (k (zeroBits _)) := rfl

/-- A query `mm` to oracle `1` is the first challenge: `firstQ (query 1 mm k) = some ⟦mm⟧`. -/
theorem firstQ_query_one (mm : Fin (ins 1) → Bool)
    (k : (Fin (outs 1) → Bool) → OracleComp (bitSpec ins outs) α) :
    firstQ (.query 1 mm k) = some (List.ofFn mm) := rfl

/-- **Once the challenge is recorded, the answer function no longer matters**:
`chRun g c (some C) = chRun g' c (some C)`.

**Proof sketch.** Induction on `c`: from a recorded state both runs answer oracle `0` with
all-`false` and oracle `1` with the recorded `C`, and keep the state. -/
theorem chRun_some_congr (g g' : (Fin (ins 1) → Bool) → List Bool)
    (c : OracleComp (bitSpec ins outs) α) (C : Fin (outs 1) → Bool) :
    chRun g c (some C) = chRun g' c (some C) := by
  induction c with
  | pure a => rfl
  | query i x k ih =>
    match i, x, k, ih with
    | 0, x, k, ih => rw [chRun_query_zero, chRun_query_zero, ih]
    | 1, x, k, ih => rw [chRun_query_one_some, chRun_query_one_some, ih]

/-- **First-challenge congruence:** if `g` and `g'` agree at the first challenge query of `c`
(vacuous when there is none), the runs from the unchallenged state agree:
`chRun g c none = chRun g' c none`.

**Proof sketch.** Induction on `c`. Queries to oracle `0` are answered all-`false` by both runs
and do not change the first challenge query. At the first query `mm` to oracle `1` both runs
record `padFin (g mm) = padFin (g' mm)`, and from then on `chRun_some_congr` applies. -/
theorem chRun_congr (g g' : (Fin (ins 1) → Bool) → List Bool)
    (c : OracleComp (bitSpec ins outs) α)
    (h : ∀ mm : Fin (ins 1) → Bool, firstQ c = some (List.ofFn mm) → g mm = g' mm) :
    chRun g c none = chRun g' c none := by
  induction c with
  | pure a => rfl
  | query i x k ih =>
    match i, x, k, ih, h with
    | 0, x, k, ih, h =>
      rw [chRun_query_zero, chRun_query_zero]
      exact ih _ fun mm hmm => h mm (by rw [firstQ_query_zero]; exact hmm)
    | 1, x, k, ih, h =>
      have hx : g x = g' x := h x (firstQ_query_one x k)
      rw [chRun_query_one_none, chRun_query_one_none, hx]
      exact chRun_some_congr g g' _ _

/-- **The first challenge query has the challenge length**: if `firstQ c = some l` then
`|l| = ins 1`.

**Proof sketch.** Induction on `c`: the first query to oracle `1` is `List.ofFn mm` with
`mm : Fin (ins 1) → Bool`. -/
theorem length_of_firstQ_eq_some (c : OracleComp (bitSpec ins outs) α) {l : List Bool}
    (h : firstQ c = some l) : l.length = ins 1 := by
  induction c with
  | pure a => exact absurd h (by rw [firstQ_pure]; exact Option.noConfusion)
  | query i x k ih =>
    match i, x, k, ih, h with
    | 0, x, k, ih, h =>
      rw [firstQ_query_zero] at h
      exact ih _ h
    | 1, x, k, _, h =>
      rw [firstQ_query_one, Option.some.injEq] at h
      rw [← h, List.length_ofFn]

/-- **Transport along equal lengths:** for a machine adversary run through `bitCodec`, if
`ins = ins'`, `outs = outs'` and `d = d'`, then
`List.ofFn (chRun (fun _ => w) (A.toCompOn (bitCodec ins outs d) n q x r) none).1 =
List.ofFn (chRun (fun _ => w) (A.toCompOn (bitCodec ins' outs' d') n q x r) none).1` and the
two runs have the same `firstQ`.

**Proof sketch.** Substitute the equalities; both sides become identical. -/
theorem chRun_toCompOn_transport {ins' outs' : Fin 2 → ℕ} {d d' : ℕ} (hi : ins = ins')
    (ho : outs = outs') (hd : d = d') (A : NUPPT) (n q : ℕ) (x : List Bool) (r : A.Coins n)
    (w : List Bool) :
    List.ofFn (chRun (ins := ins) (outs := outs) (fun _ => w)
        (A.toCompOn (bitCodec ins outs d) n q x r) none).1 =
      List.ofFn (chRun (ins := ins') (outs := outs') (fun _ => w)
        (A.toCompOn (bitCodec ins' outs' d') n q x r) none).1 ∧
    firstQ (A.toCompOn (bitCodec ins outs d) n q x r) =
      firstQ (A.toCompOn (bitCodec ins' outs' d') n q x r) := by
  subst hi ho hd
  exact ⟨rfl, rfl⟩

/-! ### Sampling identities -/

section Sampling

variable {β : Type}

/-- **Reindexing a sample by an equivalence:** `𝔼_{a ← α} g (e a) = 𝔼_{b ← β} g b`.

**Proof sketch.** Both are uniform averages (`expect_sample`); the cardinalities agree
(`Fintype.card_congr`) and the sums agree by reindexing along `e` (`Equiv.sum_comp`). -/
theorem expect_sample_equiv [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (e : α ≃ β)
    (g : β → ℝ) : expect (sample α) (fun a => g (e a)) = expect (sample β) g := by
  rw [expect_sample, expect_sample, Fintype.card_congr e, Equiv.sum_comp e g]

/-- **Sampling a product is sampling its factors:**
`𝔼_{(a, b) ← α × β} g (a, b) = 𝔼_{a ← α} 𝔼_{b ← β} g (a, b)`. -/
theorem expect_sample_prod [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (g : α × β → ℝ) :
    expect (sample (α × β)) g = expect (sample α) fun a => expect (sample β) fun b => g (a, b) := by
  rw [← Bridge.expect_sample_pair]
  simp only [expect_bind, expect_pure]

/-- **Independent samples commute:**
`𝔼_{a ← α} 𝔼_{b ← β} g a b = 𝔼_{b ← β} 𝔼_{a ← α} g a b`.

**Proof sketch.** Both are the average over the product (`expect_sample_prod`), reindexed by
the swap equivalence (`expect_sample_equiv`). -/
theorem expect_sample_comm [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (g : α → β → ℝ) :
    (expect (sample α) fun a => expect (sample β) fun b => g a b) =
      expect (sample β) fun b => expect (sample α) fun a => g a b := by
  rw [← expect_sample_prod (fun p : α × β => g p.1 p.2),
    ← expect_sample_prod (fun p : β × α => g p.2 p.1),
    ← expect_sample_equiv (Equiv.prodComm β α) (fun p : α × β => g p.1 p.2)]
  rfl

/-- **Sampling a singleton type** returns its element: `𝔼_{a ← α} g a = g default`. -/
theorem expect_sample_unique [Fintype α] [Unique α] (g : α → ℝ) :
    expect (sample α) g = g default := by
  rw [expect_sample, Fintype.card_unique, Fintype.sum_unique]
  simp

/-- Expectation is subtractive: `𝔼[f − g] = 𝔼 f − 𝔼 g`. -/
theorem expect_sub (c : ProbComp α) (f g : α → ℝ) :
    expect c (fun a => f a - g a) = expect c f - expect c g := by
  have h := expect_add c f (fun a => -1 * g a)
  rw [expect_const_mul] at h
  simp only [neg_one_mul, ← sub_eq_add_neg] at h
  exact h

/-- **The pointwise case split of the CPA reduction:** for the first challenge `(m₀, m₁)`, the
difference of the acceptance rates of `A` against `Enc(m₀)` and `Enc(m₁)` equals the difference of
the acceptance rates of the post-processed bit `(m₀ ≠ m₁) ∧ (a ≠ m₀)` against `Enc(0)` and `Enc(1)`.

**Proof sketch.** Four cases. Equal messages give `0 = 0`; `(0, 1)` gives the same difference;
`(1, 0)` gives `(1 − p₀) − (1 − p₁) = p₁ − p₀` for the negated bit. -/
theorem expect_indicator_sub {ρ : Type} [Fintype ρ] [Nonempty ρ] (f : Bool → ρ → Bool)
    (m₀ m₁ : Bool) :
    expect (sample ρ) (fun re => if f m₀ re = true then (1 : ℝ) else 0) -
        expect (sample ρ) (fun re => if f m₁ re = true then (1 : ℝ) else 0) =
      expect (sample ρ)
          (fun re => if ((m₀ != m₁) && (f false re != m₀)) = true then (1 : ℝ) else 0) -
        expect (sample ρ)
          (fun re => if ((m₀ != m₁) && (f true re != m₀)) = true then (1 : ℝ) else 0) := by
  have hneg : ∀ x : Bool, (if (!x) = true then (1 : ℝ) else 0) = 1 - if x = true then 1 else 0 := by
    intro x
    cases x <;> norm_num
  have hf : ∀ x : Bool, (x != false) = x := fun x => by cases x <;> rfl
  have ht : ∀ x : Bool, (x != true) = !x := fun x => by cases x <;> rfl
  cases m₀ <;> cases m₁
  · simp only [bne_self_eq_false, Bool.false_and, Bool.false_eq_true, if_false, expect_const,
      sub_self]
  · simp only [show (false != true) = true from rfl, Bool.true_and, hf]
  · simp only [show (true != false) = true from rfl, Bool.true_and, ht, hneg, expect_sub,
      expect_const]
    ring
  · simp only [bne_self_eq_false, Bool.false_and, Bool.false_eq_true, if_false, expect_const,
      sub_self]

end Sampling

end TCSlib.Cryptography.Composability.ChallengeSim

## ===== TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/RecordHandler.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.ChallengeSim
import TCSlib.Complexity.ClassNP.PolyTimeBlockLoop

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The recording handler of a single-challenge reduction

A reduction from CPA security to an indistinguishability assumption with one challenge
[PS10, the claim after Definition 171.5] runs the adversary once. It answers every decryption
query with `⊥` and every challenge query with the same string, its own challenge, and it
records the first challenge query `⟨m₀, m₁⟩` (two bits) to post-process the adversary's
output. This file builds that handler as a `Games.PolyHandler` (`recHandler`), generic in the
ciphertext-length polynomial and in the polynomial-time function `ans` that computes the
challenge answer from the reduction's context, so that T1 (`Games.exists_handlerMachine`) makes
it a machine.

Its simulation is the deterministic run `ChallengeSim.chRun` with the constant challenge answer
`ans ctx`, and its final state records `ChallengeSim.firstQ` (`simulate_recHandler_init`).

## Main definitions

* `ChallengeSim.recDin`, `recDout`: the query and answer lengths of the two oracles.
* `ChallengeSim.recRun`, `recOut`: the handler's step and finalization as string functions.
* `ChallengeSim.recHandler Lc ans hans`: the handler.

## Main results

* `ChallengeSim.simulate_recHandler_recorded`, `simulate_recHandler_init`: the handler's
  simulation is the deterministic run with the constant answer, and its final state records the
  first challenge query.
* `ChallengeSim.recOut_init`, `recOut_recorded`: the finalization's output bit.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.1.4, Definition 171.5 and the claim after it (book pp. 171–172).
-/

namespace TCSlib.Cryptography.Composability.ChallengeSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! ### Lengths -/

/-- The query lengths: `Lc(n)`-bit ciphertexts to oracle `0` (decryption), two-bit challenge
queries `⟨m₀, m₁⟩` to oracle `1`. -/
def recDin (Lc : PolyExpr) : Fin 2 → PolyExpr
  | 0 => Lc
  | 1 => .const 2

/-- Decryption queries have `Lc(n)` bits. -/
theorem recDin_zero (Lc : PolyExpr) : recDin Lc 0 = Lc := rfl

/-- Challenge queries have two bits. -/
theorem recDin_one (Lc : PolyExpr) : recDin Lc 1 = .const 2 := rfl

/-- The answer lengths: a two-bit decryption answer (a validity flag and one message bit) and an
`Lc(n)`-bit challenge ciphertext. -/
def recDout (Lc : PolyExpr) : Fin 2 → PolyExpr
  | 0 => .const 2
  | 1 => Lc

/-- Decryption answers have two bits. -/
theorem recDout_zero (Lc : PolyExpr) : recDout Lc 0 = .const 2 := rfl

/-- Challenge answers have `Lc(n)` bits. -/
theorem recDout_one (Lc : PolyExpr) : recDout Lc 1 = Lc := rfl

/-! ### The step function -/

/-- **One step of the recording handler** on `⟨ctx, ⟨s, ⟨1^i, x⟩⟩⟩`. A challenge query (`i = 1`)
is answered with `ans ctx`; if the state's first bit is unset, the new state is `1 :: x` (the
query recorded), otherwise the state is kept. A decryption query (`i = 0`) is answered `00` and
keeps the state. -/
def recRun (ans : List Bool → List Bool) (w : List Bool) : List Bool :=
  if (pairFstD (pairSndD (pairSndD w))).headD false then
    pairEncode (ans (pairFstD w))
      (if (pairFstD (pairSndD w)).headD false then pairFstD (pairSndD w)
        else true :: pairSndD (pairSndD (pairSndD w)))
  else pairEncode [false, false] (pairFstD (pairSndD w))

/-- The defining equation of `recRun`. -/
theorem recRun_eq (ans : List Bool → List Bool) (w : List Bool) :
    recRun ans w =
      if (pairFstD (pairSndD (pairSndD w))).headD false then
        pairEncode (ans (pairFstD w))
          (if (pairFstD (pairSndD w)).headD false then pairFstD (pairSndD w)
            else true :: pairSndD (pairSndD (pairSndD w)))
      else pairEncode [false, false] (pairFstD (pairSndD w)) := rfl

/-- A decryption query is answered `00` and keeps the state. -/
theorem recRun_dec (ans : List Bool → List Bool) (ctx s x : List Bool) :
    recRun ans (pairEncode ctx (pairEncode s (pairEncode [] x))) =
      pairEncode [false, false] s := by
  simp only [recRun_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.headD_nil,
    Bool.false_eq_true, if_false]

/-- The first challenge query `x` (state's first bit unset) is answered with `ans ctx` and
recorded as the state `1 :: x`. -/
theorem recRun_fresh (ans : List Bool → List Bool) (ctx s x : List Bool)
    (hs : s.headD false = false) :
    recRun ans (pairEncode ctx (pairEncode s (pairEncode [true] x))) =
      pairEncode (ans ctx) (true :: x) := by
  simp only [recRun_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.headD_cons, if_true, hs,
    Bool.false_eq_true, if_false]

/-- A later challenge query (state's first bit set) is answered with `ans ctx` and keeps the
state. -/
theorem recRun_recorded (ans : List Bool → List Bool) (ctx s x : List Bool)
    (hs : s.headD false = true) :
    recRun ans (pairEncode ctx (pairEncode s (pairEncode [true] x))) = pairEncode (ans ctx) s := by
  simp only [recRun_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.headD_cons, if_true, hs]

/-- The step function is polynomial-time when `ans` is. -/
theorem polyTimeComputable_recRun {ans : List Bool → List Bool} (hans : PolyTimeComputable ans) :
    PolyTimeComputable (recRun ans) := by
  have hs : PolyTimeComputable fun w => pairFstD (pairSndD w) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hq : PolyTimeComputable fun w => [(pairFstD (pairSndD (pairSndD w))).headD false] :=
    polyTimeComputable_headD.comp
      (polyTimeComputable_pairFstD.comp
        (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))
  have hh : PolyTimeComputable fun w => [(pairFstD (pairSndD w)).headD false] :=
    polyTimeComputable_headD.comp hs
  have hx : PolyTimeComputable fun w => true :: pairSndD (pairSndD (pairSndD w)) :=
    (polyTimeComputable_const [true]).append (polyTimeComputable_pairSndD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))
  exact polyTimeComputable_ite hq
    ((hans.comp polyTimeComputable_pairFstD).pairEncode (polyTimeComputable_ite hh hs hx))
    ((polyTimeComputable_const [false, false]).pairEncode hs)

/-! ### The finalization -/

/-- **The finalization** on `⟨ctx, ⟨s, a⟩⟩`, with `s = [asked, m₀, m₁]` and `a` the adversary's
bit: `[a]` if `(m₀, m₁) = (0, 1)`, `[¬a]` if `(m₀, m₁) = (1, 0)`, and `[0]` if `m₀ = m₁` or no
challenge was asked. -/
def recOut (w : List Bool) : List Bool :=
  if (pairFstD (pairSndD w)).headD false then
    if ((pairFstD (pairSndD w)).drop 1).headD false then
      if (((pairFstD (pairSndD w)).drop 1).drop 1).headD false then [false]
      else [!(pairSndD (pairSndD w)).headD false]
    else
      if (((pairFstD (pairSndD w)).drop 1).drop 1).headD false then
        [(pairSndD (pairSndD w)).headD false]
      else [false]
  else [false]

/-- The defining equation of `recOut`. -/
theorem recOut_eq (w : List Bool) :
    recOut w =
      if (pairFstD (pairSndD w)).headD false then
        if ((pairFstD (pairSndD w)).drop 1).headD false then
          if (((pairFstD (pairSndD w)).drop 1).drop 1).headD false then [false]
          else [!(pairSndD (pairSndD w)).headD false]
        else
          if (((pairFstD (pairSndD w)).drop 1).drop 1).headD false then
            [(pairSndD (pairSndD w)).headD false]
          else [false]
      else [false] := rfl

/-- Without a recorded challenge the finalization outputs `[0]`. -/
theorem recOut_init (ctx a : List Bool) :
    recOut (pairEncode ctx (pairEncode [false, false, false] a)) = [false] := by
  simp only [recOut_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.headD_cons,
    Bool.false_eq_true, if_false]

/-- With the challenge `(m₀, m₁)` recorded, the finalization outputs the bit
`(m₀ ≠ m₁) ∧ (a ≠ m₀)`: `a` for `(0, 1)`, `¬a` for `(1, 0)`, and `0` otherwise. -/
theorem recOut_recorded (ctx a : List Bool) (m₀ m₁ : Bool) :
    recOut (pairEncode ctx (pairEncode [true, m₀, m₁] a)) =
      [(m₀ != m₁) && (a.headD false != m₀)] := by
  simp only [recOut_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.headD_cons, if_true,
    List.drop_succ_cons, List.drop_zero]
  cases m₀ <;> cases m₁ <;> cases a.headD false <;> rfl

/-- The finalization is polynomial-time. -/
theorem polyTimeComputable_recOut : PolyTimeComputable recOut := by
  have hs : PolyTimeComputable fun w => pairFstD (pairSndD w) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hs₁ : PolyTimeComputable fun w => (pairFstD (pairSndD w)).drop 1 :=
    polyTimeComputable_tail.comp hs
  have hs₂ : PolyTimeComputable fun w => ((pairFstD (pairSndD w)).drop 1).drop 1 :=
    polyTimeComputable_tail.comp hs₁
  have ha : PolyTimeComputable fun w => [(pairSndD (pairSndD w)).headD false] :=
    polyTimeComputable_headD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  exact polyTimeComputable_ite (polyTimeComputable_headD.comp hs)
    (polyTimeComputable_ite (polyTimeComputable_headD.comp hs₁)
      (polyTimeComputable_ite (polyTimeComputable_headD.comp hs₂) (polyTimeComputable_const _)
        (polyTimeComputable_not ha))
      (polyTimeComputable_ite (polyTimeComputable_headD.comp hs₂) ha (polyTimeComputable_const _)))
    (polyTimeComputable_const _)

/-! ### The handler -/

/-- The adversary's input: the first component `pk` of the reduction input `z = ⟨pk, c⟩`, read
from the context `⟨1^n, ⟨z, ω⟩⟩`. -/
def recAdvIn (ctx : List Bool) : List Bool := pairFstD (pairFstD (pairSndD ctx))

/-- The defining equation of `recAdvIn`. -/
theorem recAdvIn_eq (ctx : List Bool) : recAdvIn ctx = pairFstD (pairFstD (pairSndD ctx)) := rfl

/-- **The recording handler** with ciphertext length `Lc` and challenge answer `ans ctx`: three
state bits `[asked, m₀, m₁]`, initially `000`; no seed; the adversary runs on `pk`, the first
component of the reduction input; decryption queries are answered `00`; challenge queries are
answered `ans ctx`, and the first one is recorded; the output is `recOut`. -/
noncomputable def recHandler (Lc : PolyExpr) (ans : List Bool → List Bool)
    (hans : PolyTimeComputable ans) : PolyHandler 2 (recDin Lc) (recDout Lc) where
  stateLen := .const 3
  seedLen := .const 0
  init _ := zeroBits _
  run := recRun ans
  poly := polyTimeComputable_recRun hans
  advIn := recAdvIn
  advIn_poly := polyTimeComputable_pairFstD.comp
    (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
  out := recOut
  out_poly := polyTimeComputable_recOut

attribute [simps (config := { isSimp := false }) stateLen seedLen init run advIn out] recHandler

/-! ### The handler's simulation -/

section Simulation

variable {α : Type} (Lc : PolyExpr) {ans : List Bool → List Bool} (hans : PolyTimeComputable ans)
  (n : ℕ) (z : List Bool) (ω : Fin ((recHandler Lc ans hans).seedLen.eval n) → Bool)

/-- **After the challenge is recorded**, the handler's simulation is the deterministic run with
the constant challenge answer `w = ans ⟨1^n, ⟨z, ω⟩⟩` from the recorded state `padFin w`, and the
handler's state does not change. Requires `|w| = Lc(n)`.

**Proof sketch.** Induction on the computation. A decryption query is answered `00`
(`recRun_dec`), the all-`false` answer of `chRun`; a challenge query is answered `w`
(`recRun_recorded`), which is `padFin w` at length `Lc(n)`; the state is kept in both cases. -/
theorem simulate_recHandler_recorded
    (hw : (ans (seedIn n z (List.ofFn ω))).length = Lc.eval n)
    (c : OracleComp (bitSpecAt (recDin Lc) (recDout Lc) n) α)
    (s : Fin ((recHandler Lc ans hans).stateLen.eval n) → Bool)
    (hs : (List.ofFn s).headD false = true) :
    simulate ((recHandler Lc ans hans).impl n z ω) c s =
      .pure ((chRun (fun _ => ans (seedIn n z (List.ofFn ω))) c
        (some (padFin _ (ans (seedIn n z (List.ofFn ω)))))).1, s) := by
  induction c with
  | pure a => rw [simulate_pure, chRun_pure]
  | query i x k ih =>
    match i, x, k, ih with
    | 0, x, k, ih =>
      have hans0 : (recHandler Lc ans hans).answer n z ω s 0 x = (zeroBits _, s) := by
        refine PolyHandler.answer_of_run_eq _ ?_
        rw [recHandler_run, PolyHandler.input_eq, ofFn_zeroBits]
        simp only [recDout_zero, PolyExpr.eval_const]
        exact recRun_dec ans _ _ _
      rw [simulate_query, PolyHandler.impl_apply, hans0, OracleComp.pure_bind, chRun_query_zero]
      exact ih _
    | 1, x, k, ih =>
      have hans1 : (recHandler Lc ans hans).answer n z ω s 1 x =
          (padFin _ (ans (seedIn n z (List.ofFn ω))), s) := by
        refine PolyHandler.answer_of_run_eq _ ?_
        rw [recHandler_run, PolyHandler.input_eq, GGMRed.ofFn_padFin_of_length (by
          rw [hw, recDout_one]), seedIn_eq]
        exact recRun_recorded ans _ _ _ hs
      rw [simulate_query, PolyHandler.impl_apply, hans1, OracleComp.pure_bind,
        chRun_query_one_some]
      exact ih _

/-- **The handler's simulation from its initial state** is the deterministic run with the
constant challenge answer `w = ans ⟨1^n, ⟨z, ω⟩⟩` from the unchallenged state, and its final
state is `000` if no challenge was asked and `1 :: mm` for the first challenge query `mm`
(`firstQ`). Requires `|w| = Lc(n)`.

**Proof sketch.** Induction on the computation. Decryption queries are answered `00` and keep
the initial state `000`. The first challenge query `x` is answered `w`, which is `padFin w`, and
records the state `1 :: x`; from there `simulate_recHandler_recorded` applies. -/
theorem simulate_recHandler_init
    (hw : (ans (seedIn n z (List.ofFn ω))).length = Lc.eval n)
    (c : OracleComp (bitSpecAt (recDin Lc) (recDout Lc) n) α) :
    ∃ s : Fin ((recHandler Lc ans hans).stateLen.eval n) → Bool,
      simulate ((recHandler Lc ans hans).impl n z ω) c ((recHandler Lc ans hans).init n) =
          .pure ((chRun (fun _ => ans (seedIn n z (List.ofFn ω))) c none).1, s) ∧
        List.ofFn s = (firstQ c).elim [false, false, false] (true :: ·) := by
  have hinit : List.ofFn ((recHandler Lc ans hans).init n) = [false, false, false] := by
    rw [show (recHandler Lc ans hans).init n = zeroBits _ from
        funext (recHandler_init Lc ans hans n),
      ofFn_zeroBits, recHandler_stateLen, PolyExpr.eval_const]
    rfl
  induction c with
  | pure a => exact ⟨_, by rw [simulate_pure, chRun_pure], by rw [firstQ_pure]; exact hinit⟩
  | query i x k ih =>
    match i, x, k, ih with
    | 0, x, k, ih =>
      have hans0 : (recHandler Lc ans hans).answer n z ω ((recHandler Lc ans hans).init n) 0 x =
          (zeroBits _, (recHandler Lc ans hans).init n) := by
        refine PolyHandler.answer_of_run_eq _ ?_
        rw [recHandler_run, PolyHandler.input_eq, ofFn_zeroBits]
        simp only [recDout_zero, PolyExpr.eval_const]
        exact recRun_dec ans _ _ _
      obtain ⟨s, hsim, hs⟩ := ih (zeroBits _)
      refine ⟨s, ?_, ?_⟩
      · rw [simulate_query, PolyHandler.impl_apply, hans0, OracleComp.pure_bind, chRun_query_zero]
        exact hsim
      · rw [firstQ_query_zero]
        exact hs
    | 1, x, k, _ =>
      have hlen : (true :: List.ofFn x).length = (recHandler Lc ans hans).stateLen.eval n := by
        rw [List.length_cons, List.length_ofFn, recHandler_stateLen]
        simp only [recDin_one, PolyExpr.eval_const]
      have hans1 : (recHandler Lc ans hans).answer n z ω ((recHandler Lc ans hans).init n) 1 x =
          (padFin _ (ans (seedIn n z (List.ofFn ω))), padFin _ (true :: List.ofFn x)) := by
        refine PolyHandler.answer_of_run_eq _ ?_
        rw [recHandler_run, PolyHandler.input_eq, GGMRed.ofFn_padFin_of_length (by
          rw [hw, recDout_one]), GGMRed.ofFn_padFin_of_length hlen, seedIn_eq]
        refine recRun_fresh ans _ _ _ ?_
        rw [hinit]
        rfl
      refine ⟨padFin _ (true :: List.ofFn x), ?_, ?_⟩
      · rw [simulate_query, PolyHandler.impl_apply, hans1, OracleComp.pure_bind,
          chRun_query_one_none]
        exact simulate_recHandler_recorded Lc hans n z ω hw _ _
          (by rw [GGMRed.ofFn_padFin_of_length hlen]; rfl)
      · rw [GGMRed.ofFn_padFin_of_length hlen, firstQ_query_one]
        rfl

end Simulation

end TCSlib.Cryptography.Composability.ChallengeSim

## ===== TCSlib/Cryptography/Games/Efficiency.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Cryptography.Games.Probability
import TCSlib.Cryptography.Games.Bridges.Machines
import TCSlib.Cryptography.Games.Efficiency.Strings
import TCSlib.Cryptography.Games.Efficiency.Replay
import TCSlib.Cryptography.Games.Efficiency.Handler
import TCSlib.Cryptography.Games.Efficiency.OracleBridge
import TCSlib.Cryptography.Games.Efficiency.Interactive
import TCSlib.Cryptography.Games.Efficiency.InteractiveSpec

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The efficiency of reductions

A reduction runs a machine adversary `A` and answers `A`'s queries with a polynomial-time
**handler**. Proved once, the targets below say that the result is again a machine, so the
hardness assumptions, which quantify over machines (`Complexity.NUPPT`), apply to it. The route is
`briefs/pass-shelat-ch5-8/design/S2b-efficiency.md`. The template is Frederick Dehmel's GGM
reduction machine (`Asymptotic/GGMReduction*.lean`), whose loop `GGMRed.stateLoopFun` is reused.

**Status: proved.** The definitions (T0) are final. The statements of T1, T2 and T4 and of the
companion `exists_toCompOn_of_toComp` were frozen at the issue of the fill brief
(`briefs/pass-shelat-ch5-8/fills/efficiency/`); the efficiency fill (`s2b-efficiency`) proved them,
with the helper modules below (namespace `TCSlib.Cryptography.Games.EffFill`).

## Contents

* `Games.Efficiency.Strings`: the string layer (log append, fixed-length decoding, the canonical
  decoder, the activation loop over `GGMRed.stateLoopFun`, the machine glue).
* `Games.Efficiency.Replay`: replaying a computation with a next-move function; cost scaling.
* `Games.Efficiency.Handler`: the machine of a non-interactive handler (T1).
* `Games.Efficiency.OracleBridge`: the translators to next-query machines (T4).
* `Games.Efficiency.Interactive`: the replay machine of an interactive handler (T2).
* `Games.Efficiency.InteractiveSpec`: its functional equation (T2).

## The shape of a reduction

A handler describes everything a reduction does around one run of the adversary. At parameter
`n` the reduction has an input `z` and a seed `ω` (its own coins). Every function of the handler
reads them from the **context** `⟨1^n, ⟨z, ω⟩⟩` (`seedIn`):
1. **the adversary's input** is a polynomial-time function of the context (`advIn`), for example
   a public key built from `z` and `ω`; the adversary runs as `A.toCompOn` on it;
2. **each query** of the adversary is answered from the handler's state, by the handler alone
   (`PolyHandler`) or with queries to the reduction's own oracles (`InteractiveHandler`);
3. **the reduction's output** is computed from the context, the final state and the adversary's
   output: by a polynomial-time function (`PolyHandler.out`), or by a last phase that may itself
   query the reduction's oracles, within its own budget (`InteractiveHandler.finish`).

## Fixed lengths

Every length is an explicit polynomial in the parameter `n`: queries and answers (`din i`,
`dout i`), the adversary's output (`dα`), the handler's state and seed, and, for an interactive
handler, the reduction's output. This bounds every history, which the guarded state loop needs.

## Scope

* **Covered:** a reduction that runs one adversary once, on an input computed from its own,
  answers the adversary's queries with or without its own oracles, and post-processes the final
  state and the adversary's output (with further oracle queries if it is interactive). T1 makes
  the machine's output exactly the finalized output; T2 makes the machine's computation exactly
  the simulation followed by the finalization, with the budgets added.
* **Adversaries without input** are adversaries with an input they ignore
  (`exists_toCompOn_of_toComp`).
* **Reductions to a pseudorandom function** reach `OracleEnsemble.Indist` through T4: an oracle
  machine against one bit-string oracle with a one-bit output is, on evaluations, a next-query
  machine of the ch. 2–4 layer (`NUPPT.toOracleAdversary`).
* **Non-uniform handlers** (for example one that runs a non-uniform distinguisher) receive their
  advice through the input `z`; it is hard-wired into the machine afterwards
  (`NUPPT.exists_withAdvice`, with `NUPPT.exists_comp` to re-pair the input).
* **Not covered:** reductions that rewind the adversary or run it more than once, and variable
  lengths.

## Main definitions

* `Games.seedIn n z ω`: the context `⟨1^n, ⟨z, ω⟩⟩`.
* `Games.PolyHandler k din dout`: a polynomial-time handler for `k` bit-string oracles, with its
  state and seed lengths, initial state, adversary input and finalization.
* `Games.PolyHandler.answer`, `Games.PolyHandler.impl`: its answers, and its semantics as a
  stateful `QueryImpl` that asks no oracle, at parameter `n`, reduction input `z` and seed `ω`;
  `PolyHandler.advInput` and `PolyHandler.result`: the adversary's input and the reduction's
  output.
* `Games.InteractiveHandler`, `InteractiveHandler.call`, `InteractiveHandler.impl`: a
  polynomial-time handler that may itself query outer bit-string oracles, up to `perCall(n)`
  times per inner query, and its semantics as a `QueryImpl` of the inner oracles by the outer ones;
  `InteractiveHandler.advInput` and `InteractiveHandler.finish`: the adversary's input and the
  finalization, with up to `finCall(n)` outer queries.

## Main results

* `Games.exists_handlerMachine` (T1, the fill's target): a reduction with a polynomial-time
  handler is a machine, whose output is exactly the finalized output of the simulation.
* `Games.exists_interactiveHandlerMachine` (T2, the fill's target): a reduction with an
  interactive handler is an oracle machine against the outer oracles, with budget
  `q(n) · perCall(n) + finCall(n)`, whose computation is exactly the simulation followed by the
  finalization. The reductions that forward or answer queries with their own oracle need it (the
  PRF MAC's distinguisher, hash-and-sign's forger, the CPA and CCA reductions).
* `Games.exists_toCompOn_of_toComp` (the fill's target): a machine without input is a machine
  with an input that it ignores, with the same coins.
* `Games.exists_toOracleAdversary_of_bitCodec` (T4, the fill's target): an oracle machine
  against one `bitCodec` oracle with a one-bit output, on the empty input, evaluates as a
  next-query machine of the ch. 2–4 layer.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010:
  every reduction of ch. 5–8 (for example the proofs of Thms 135.4 and 168.2).
-/

namespace TCSlib.Cryptography.Games

open Complexity Turing

variable {k : ℕ}

/-- The bit-string oracles at parameter `n`, with polynomial lengths. -/
abbrev bitSpecAt (din dout : Fin k → PolyExpr) (n : ℕ) : OracleSpec (Fin k) :=
  bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n)

/-- The bit-string oracles at parameter `n` are `bitSpec` of the evaluated lengths:
`bitSpecAt din dout n = bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n)`. -/
theorem bitSpecAt_eq (din dout : Fin k → PolyExpr) (n : ℕ) :
    bitSpecAt din dout n = bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n) :=
  rfl

/-- The **context** of a reduction at parameter `n`, with the reduction's input `z` and its seed
`ω`: the string `⟨1^n, ⟨z, ω⟩⟩`. Every function of a handler reads it. -/
def seedIn (n : ℕ) (z ω : List Bool) : List Bool :=
  pairEncode (List.replicate n true) (pairEncode z ω)

/-- The context is `⟨1^n, ⟨z, ω⟩⟩`:
`seedIn n z ω = pairEncode (List.replicate n true) (pairEncode z ω)`. -/
theorem seedIn_eq (n : ℕ) (z ω : List Bool) :
    seedIn n z ω = pairEncode (List.replicate n true) (pairEncode z ω) :=
  rfl

/-- A **polynomial-time handler** for `k` bit-string oracles with query lengths `din` and answer
lengths `dout`: a reduction that runs the adversary once and answers its queries by itself. Its
three functions are polynomial-time, and each reads the context `⟨1^n, ⟨z, ω⟩⟩` (`seedIn`: the
parameter, the reduction's input `z` and its seed `ω`):
- `advIn` maps the context to the adversary's input;
- `run` answers one query: on `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨1^i, x⟩⟩⟩` (the context, the state `s`, and
  the query `x` to oracle `i`), it returns `⟨y, s'⟩`, the answer and the new state;
- `out` maps `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, a⟩⟩` (the context, the final state and the adversary's output)
  to the reduction's output. -/
structure PolyHandler (k : ℕ) (din dout : Fin k → PolyExpr) where
  /-- The length of the state. -/
  stateLen : PolyExpr
  /-- The length of the seed (the handler's own coins). -/
  seedLen : PolyExpr
  /-- The initial state at each parameter. -/
  init : ∀ n, Fin (stateLen.eval n) → Bool
  /-- The handler as a string function. -/
  run : List Bool → List Bool
  /-- It is polynomial-time computable. -/
  poly : PolyTimeComputable run
  /-- The adversary's input, as a function of the context `⟨1^n, ⟨z, ω⟩⟩` (for example a public
  key built from `z` and the seed). For an adversary without input it is ignored. -/
  advIn : List Bool → List Bool
  /-- The adversary's input is polynomial-time computable. -/
  advIn_poly : PolyTimeComputable advIn
  /-- The finalization: the reduction's output, as a function of `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, a⟩⟩` (the
  context, the final state `s` and the adversary's output `a`). -/
  out : List Bool → List Bool
  /-- The finalization is polynomial-time computable. -/
  out_poly : PolyTimeComputable out

namespace PolyHandler

variable {din dout : Fin k → PolyExpr}

/-- The handler's input string for the query `x` to oracle `i` in state `s`. -/
def input (n : ℕ) (z : List Bool) (ω : List Bool) (s : List Bool) (i : Fin k) (x : List Bool) :
    List Bool :=
  pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
    (pairEncode s (pairEncode (List.replicate i true) x))

/-- The handler's input string is `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨1^i, x⟩⟩⟩`. -/
theorem input_eq (n : ℕ) (z ω s : List Bool) (i : Fin k) (x : List Bool) :
    input n z ω s i x =
      pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
        (pairEncode s (pairEncode (List.replicate i true) x)) :=
  rfl

/-- The adversary's input at parameter `n`, for the reduction input `z` and the seed `ω`: `advIn`
of the context `⟨1^n, ⟨z, ω⟩⟩`. -/
def advInput (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) : List Bool :=
  H.advIn (seedIn n z (List.ofFn ω))

/-- The adversary's input is `advIn` of the context:
`H.advInput n z ω = H.advIn (seedIn n z (List.ofFn ω))`. -/
theorem advInput_eq (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) :
    H.advInput n z ω = H.advIn (seedIn n z (List.ofFn ω)) :=
  rfl

/-- The reduction's output at parameter `n`, for the reduction input `z` and the seed `ω`, when
the final state is `s` and the adversary's output is `a`: `out` of
`⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, a⟩⟩`. -/
def result (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool) : List Bool :=
  H.out (pairEncode (seedIn n z (List.ofFn ω)) (pairEncode (List.ofFn s) (List.ofFn a)))

/-- The reduction's output is `out` of the context, the final state and the adversary's output:
`H.result n z ω s a = H.out (pairEncode (seedIn n z (List.ofFn ω))
(pairEncode (List.ofFn s) (List.ofFn a)))`. -/
theorem result_eq (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool) :
    H.result n z ω s a =
      H.out (pairEncode (seedIn n z (List.ofFn ω)) (pairEncode (List.ofFn s) (List.ofFn a))) :=
  rfl

/-- The handler's answer and new state, decoded with fixed lengths. If `run`'s output is not a
pair, both are all-`false`; otherwise each component of the wrong length is replaced by
all-`false` independently (a total default; well-behaved handlers never produce one). An
interactive handler defaults jointly instead (`InteractiveHandler`). -/
def answer (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) (i : Fin k)
    (x : Fin ((din i).eval n) → Bool) :
    (Fin ((dout i).eval n) → Bool) × (Fin (H.stateLen.eval n) → Bool) :=
  match pairDecode (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x))) with
  | some (yw, sw) =>
    ((decodeFin _ yw).getD (zeroBits _), (decodeFin _ sw).getD (zeroBits _))
  | none => (zeroBits _, zeroBits _)

section Answer

variable (H : PolyHandler k din dout) {n : ℕ} {z : List Bool} {ω : Fin (H.seedLen.eval n) → Bool}
  {s : Fin (H.stateLen.eval n) → Bool} {i : Fin k} {x : Fin ((din i).eval n) → Bool}

/-- If `run`'s output is not a pair, the answer and the new state are all-`false`. -/
theorem answer_of_pairDecode_eq_none
    (h : pairDecode (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x))) = none) :
    H.answer n z ω s i x = (zeroBits _, zeroBits _) := by
  unfold answer
  rw [h]

/-- If `run`'s output is the pair `⟨yw, sw⟩`, the answer is `yw` and the new state `sw`, each
decoded with its fixed length and all-`false` if that length is wrong:
`H.answer n z ω s i x = ((decodeFin _ yw).getD (zeroBits _), (decodeFin _ sw).getD (zeroBits _))`.
-/
theorem answer_of_pairDecode_eq_some {yw sw : List Bool}
    (h : pairDecode (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x))) =
      some (yw, sw)) :
    H.answer n z ω s i x =
      ((decodeFin _ yw).getD (zeroBits _), (decodeFin _ sw).getD (zeroBits _)) := by
  unfold answer
  rw [h]

/-- **A well-formed output:** if `run` returns `⟨y, s'⟩` with `y` and `s'` of the fixed lengths,
the answer is `y` and the new state `s'`. -/
theorem answer_of_run_eq {y : Fin ((dout i).eval n) → Bool} {s' : Fin (H.stateLen.eval n) → Bool}
    (h : H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)) =
      pairEncode (List.ofFn y) (List.ofFn s')) :
    H.answer n z ω s i x = (y, s') := by
  have h' : pairDecode (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x))) =
      some (List.ofFn y, List.ofFn s') := by
    rw [h, pairDecode_pairEncode]
  rw [answer_of_pairDecode_eq_some H h', decodeFin_ofFn, decodeFin_ofFn, Option.getD_some,
    Option.getD_some]

end Answer

/-- The handler as an implementation of the bit-string oracles at parameter `n`, for the
reduction input `z` and seed `ω`: it keeps its state and asks no oracle (the non-interactive
case). -/
def impl (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) :
    QueryImpl (bitSpecAt din dout n) (Fin (H.stateLen.eval n) → Bool) unifSpec :=
  fun i x s => .pure (H.answer n z ω s i x)

/-- The handler answers the query `x` to oracle `i` in state `s` with no coins and no queries:
`H.impl n z ω i x s = pure (H.answer n z ω s i x)`. -/
theorem impl_apply (H : PolyHandler k din dout) (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (i : Fin k) (x : Fin ((din i).eval n) → Bool)
    (s : Fin (H.stateLen.eval n) → Bool) :
    H.impl n z ω i x s = .pure (H.answer n z ω s i x) :=
  rfl

end PolyHandler

/-- **T1 (the efficiency fill's target; non-interactive handlers).** For a machine adversary `A`
with query budget `q` and `dα`-bit outputs against `k` bit-string oracles, and a polynomial-time
handler `H`, there is a machine `B` and, at every parameter, a bijection `φ` from (the handler's
seed, `A`'s coins) to `B`'s coins, with the following property. Run `A` on the input
`H.advInput n z ω`, answer its queries by `H` (input `z`, seed `ω`) from `H`'s initial state, and
let `a` be `A`'s output and `s` the final state. Then `B`'s output on input `z` with coins
`φ (ω, r)` is exactly the reduction's output `H.result n z ω s a`.

**Proof sketch** (the fill's; route note §"T1").
1. `B`'s raw function is the activation loop `EffFill.hRaw` (`GGMRed.stateLoopFun` through
   `EffFill.actLoop`) on the layout `⟨⟨⟨1^n, ⟨z, ω⟩⟩, ⟨α_A, s₀⟩⟩, r⟩`. The initial state
   `s₀ = H.init n` is part of the advice, beside `A`'s advice `α_A`, since `init` is an arbitrary
   function of `n`; so `B` is non-uniform even when `A` is uniform. The loop state is
   `⟨L, ⟨s, 1^t⟩⟩` (`A`'s encoded log, `H`'s state, the answered queries); the context
   `seedIn n z ω` and `A`'s input are recomputed in every round.
2. A round runs `A` on `⟨A's input, L⟩` (`NUPPT.polyTimeComputable_output`) and reads its move
   through the canonical decoder `EffFill.canonWord`, which returns the canonical word of
   `decodeBitMove`'s move on every word (`EffFill.canonWord_eq`, canonicity tested by re-encoding).
   It stops with `H.out ⟨ctx, ⟨s, a⟩⟩` on an output `a`, and with `H.out ⟨ctx, ⟨s, 0^{dα(n)}⟩⟩` on a
   query when `t = q(n)`. Otherwise it feeds the query to `H.run`, decodes the answer and the new
   state componentwise (`EffFill.fixLen`, `EffFill.ofFn_getD_decodeFin` and the `answer` lemmas),
   and appends the entry to `L` (`EffFill.encodeLog_append_single`).
3. At most `q(n) + 1` rounds, with states of polynomial length (all lengths are fixed), so the raw
   function is polynomial-time (`EffFill.hRaw_poly`, from `GGMRed.stateLoopFun_poly`).
4. The functional equation (`EffFill.hRaw_spec`): by induction on the remaining budget, the loop's
   state after `t` rounds encodes the simulation after `t` queries (`toCompOn_eq`, `buildComp`'s
   case lemmas, `simulate_query`, `PolyHandler.impl_apply`); `GGMRed.stateLoopFun_eval` reads off
   the output (`EffFill.runsTo_stop`), and `result_eq` and `seedIn_eq` identify it.
5. `B` is `NUPPT.ofPolyTime` of the raw function followed by `NUPPT.exists_split` with
   `p = H.seedLen` (`EffFill.exists_splitMachine`); `φ` appends the seed and the coins. -/
theorem exists_handlerMachine (A : NUPPT) (q : PolyExpr) (din dout : Fin k → PolyExpr)
    (dα : PolyExpr) (H : PolyHandler k din dout) :
    ∃ B : NUPPT, ∀ n : ℕ, ∃ φ : (Fin (H.seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n,
      ∀ (z : List Bool) (ω : Fin (H.seedLen.eval n) → Bool) (r : A.Coins n),
        ∃ (a : Fin (dα.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool),
          simulate (H.impl n z ω)
              (A.toCompOn
                (bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n))
                n (q.eval n) (H.advInput n z ω) r) (H.init n) = .pure (a, s) ∧
            B.runAt n z (φ (ω, r)) = H.result n z ω s a := by
  -- The machine: the handler loop of `EffFill.hRaw`, with `⟨A.advice n, s₀⟩` as advice and the
  -- seed passed as data.
  obtain ⟨B, hB⟩ := EffFill.exists_splitMachine A
    (EffFill.hRaw_poly A q dα din dout H.stateLen H.poly H.advIn_poly H.out_poly)
    (.add (.add (.mul (.const 2) A.adv) (.const 2)) H.stateLen)
    (fun n => pairEncode (A.advice n) (List.ofFn (H.init n))) (fun n => by
      rw [length_pairEncode, List.length_ofFn]
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
      have := A.advice_length n
      omega) H.seedLen
  refine ⟨B, fun n => ?_⟩
  obtain ⟨φ, hφ⟩ := hB n
  refine ⟨φ, fun z ω r => ?_⟩
  -- The handler's answers are `run`'s output decoded componentwise.
  have hans : ∀ (i : Fin k) (x : Fin ((din i).eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool),
      List.ofFn (H.answer n z ω s i x).1 = EffFill.fixLen ((dout i).eval n) (pairFstD (H.run
        (pairEncode (pairEncode (List.replicate n true) (pairEncode z (List.ofFn ω)))
          (pairEncode (List.ofFn s) (pairEncode (List.replicate i true) (List.ofFn x)))))) ∧
      List.ofFn (H.answer n z ω s i x).2 = EffFill.fixLen (H.stateLen.eval n) (pairSndD (H.run
        (pairEncode (pairEncode (List.replicate n true) (pairEncode z (List.ofFn ω)))
          (pairEncode (List.ofFn s) (pairEncode (List.replicate i true) (List.ofFn x)))))) := by
    intro i x s
    rw [← PolyHandler.input_eq]
    cases h : pairDecode (H.run (PolyHandler.input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)))
      with
    | none =>
      rw [PolyHandler.answer_of_pairDecode_eq_none H h, pairFstD_of_pairDecode_eq_none h,
        pairSndD_of_pairDecode_eq_none h, EffFill.fixLen_nil, EffFill.fixLen_nil, ofFn_zeroBits,
        ofFn_zeroBits]
      exact ⟨rfl, rfl⟩
    | some p =>
      obtain ⟨yw, sw⟩ := p
      rw [PolyHandler.answer_of_pairDecode_eq_some H h, eq_pairEncode_of_pairDecode _ _ _ h,
        pairFstD_pairEncode, pairSndD_pairEncode, EffFill.ofFn_getD_decodeFin,
        EffFill.ofFn_getD_decodeFin]
      exact ⟨rfl, rfl⟩
  obtain ⟨a, s, hsim, hraw⟩ := EffFill.hRaw_spec A q dα din dout H.stateLen H.run H.advIn H.out
    (spec' := unifSpec) n z (List.ofFn ω) r (H.init n) (fun i x s => H.answer n z ω s i x) hans
  refine ⟨a, s, ?_, ?_⟩
  · have himpl : H.impl n z ω = fun i x s => OracleComp.pure (H.answer n z ω s i x) := by
      funext i x s
      exact H.impl_apply n z ω i x s
    rw [himpl, PolyHandler.advInput_eq, seedIn_eq]
    exact hsim
  · rw [hφ, hraw, PolyHandler.result_eq, seedIn_eq]

/-! ### Interactive handlers (T2) -/

variable {k' : ℕ}

/-- A **polynomial-time interactive handler** for `k` inner bit-string oracles that may itself
query `k'` outer bit-string oracles. Like `PolyHandler`, it computes the adversary's input from
the context `⟨1^n, ⟨z, ω⟩⟩` (`advIn`); it answers the adversary's queries (`run`), and computes the
reduction's output in a last phase (`finRun`), both with outer queries.

One inner query `x` to oracle `i` is answered with at most `perCall(n)` outer queries, in at most
`perCall(n) + 1` rounds of `run` (the last returns the answer; a further query after the budget
is spent is cut off with the default). In each round, `run` sees `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`, where `L` is
the outer log of the call so far (encoded as `bitCodec` encodes logs), and returns a move in
`bitCodec`'s format: a query `⟨[false], ⟨1^j, x'⟩⟩` to outer oracle `j`, or the answer
`⟨[true], y ‖ s'⟩` (the inner answer, then the new state). A malformed round output, including a
payload `y ‖ s'` of the wrong total length, gives the all-`false` answer and state together (a
joint default, unlike `PolyHandler.answer`, which defaults each component separately).

The finalization works the same way on `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩` (the final state, the
adversary's output and the outer log of the finalization so far), with at most `finCall(n)` outer
queries; it returns the reduction's `outLen(n)`-bit output as `⟨[true], b⟩`, the all-`false`
output on a malformed round output or on a further query after the budget is spent. (A return at
zero remaining budget is accepted: only a query then hits the timeout.) -/
structure InteractiveHandler (k : ℕ) (din dout : Fin k → PolyExpr) (k' : ℕ)
    (din' dout' : Fin k' → PolyExpr) where
  /-- The length of the state. -/
  stateLen : PolyExpr
  /-- The length of the seed. -/
  seedLen : PolyExpr
  /-- The bound on outer queries per inner query. -/
  perCall : PolyExpr
  /-- The initial state at each parameter. -/
  init : ∀ n, Fin (stateLen.eval n) → Bool
  /-- One round of the handler, as a string function. -/
  run : List Bool → List Bool
  /-- It is polynomial-time computable. -/
  poly : PolyTimeComputable run
  /-- The adversary's input, as a function of the context `⟨1^n, ⟨z, ω⟩⟩`. For an adversary
  without input it is ignored. -/
  advIn : List Bool → List Bool
  /-- The adversary's input is polynomial-time computable. -/
  advIn_poly : PolyTimeComputable advIn
  /-- The length of the reduction's output. -/
  outLen : PolyExpr
  /-- The bound on the outer queries of the finalization. -/
  finCall : PolyExpr
  /-- One round of the finalization, as a string function: on `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩` it
  returns an outer query `⟨[false], ⟨1^j, x'⟩⟩` or the reduction's output `⟨[true], b⟩`. -/
  finRun : List Bool → List Bool
  /-- The finalization's round is polynomial-time computable. -/
  finRun_poly : PolyTimeComputable finRun

namespace InteractiveHandler

variable {din dout : Fin k → PolyExpr} {din' dout' : Fin k' → PolyExpr}

/-- The handler's input string for one round. -/
def input (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) : List Bool :=
  pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
    (pairEncode s (pairEncode (pairEncode (List.replicate i true) x) L))

/-- The handler's input string for one round is `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`. -/
theorem input_eq (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :
    input n z ω s i x L =
      pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
        (pairEncode s (pairEncode (pairEncode (List.replicate i true) x) L)) :=
  rfl

/-- The adversary's input at parameter `n`, for the reduction input `z` and the seed `ω`: `advIn`
of the context `⟨1^n, ⟨z, ω⟩⟩`. -/
def advInput (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) : List Bool :=
  H.advIn (seedIn n z (List.ofFn ω))

/-- The adversary's input is `advIn` of the context:
`H.advInput n z ω = H.advIn (seedIn n z (List.ofFn ω))`. -/
theorem advInput_eq (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) :
    H.advInput n z ω = H.advIn (seedIn n z (List.ofFn ω)) :=
  rfl

/-- **One call** of the handler on the inner query `x` to oracle `i` in state `s`: at most
`perCall(n)` outer queries, in at most `perCall(n) + 1` rounds of `run`. A malformed round output
is the all-`false` answer and state (`decodeBitMove`'s default), and so is a further query after
the budget is spent (a return at zero remaining budget is accepted). -/
def call (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) (i : Fin k)
    (x : Fin ((din i).eval n) → Bool) :
    OracleComp (bitSpecAt din' dout' n) (Fin ((dout i).eval n + H.stateLen.eval n) → Bool) :=
  buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n) _
      (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)
        ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))
    (zeroBits _) (H.perCall.eval n) []

/-- One call is `buildComp` of the handler's rounds, from the empty outer log, with budget
`perCall(n)` and the all-`false` result on a query after it is spent: `H.call n z ω s i x =
buildComp (fun L => decodeBitMove _ _ _ (H.run (input … L))) (zeroBits _) (H.perCall.eval n) []`.
-/
theorem call_eq (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) (i : Fin k)
    (x : Fin ((din i).eval n) → Bool) :
    H.call n z ω s i x =
      buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
          ((dout i).eval n + H.stateLen.eval n)
          (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)
            ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))
        (zeroBits _) (H.perCall.eval n) [] :=
  rfl

/-- The interactive handler as an implementation of the inner oracles by the outer ones, at
parameter `n`, reduction input `z` and seed `ω`: one `call` per inner query, its result split
into the answer and the new state. -/
def impl (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) :
    QueryImpl (bitSpecAt din dout n) (Fin (H.stateLen.eval n) → Bool) (bitSpecAt din' dout' n) :=
  fun i x s => (H.call n z ω s i x).bind fun w =>
    .pure (fun j => w (Fin.castAdd _ j), fun j => w (Fin.natAdd _ j))

/-- The inner query `x` to oracle `i` in state `s` is answered by one `call`, whose result is
split into the answer (its first `dout i` bits) and the new state (the rest):
`H.impl n z ω i x s = (H.call n z ω s i x).bind fun w =>
pure (fun j => w (Fin.castAdd _ j), fun j => w (Fin.natAdd _ j))`. -/
theorem impl_apply (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (i : Fin k) (x : Fin ((din i).eval n) → Bool)
    (s : Fin (H.stateLen.eval n) → Bool) :
    H.impl n z ω i x s =
      (H.call n z ω s i x).bind fun w =>
        .pure (fun j => w (Fin.castAdd _ j), fun j => w (Fin.natAdd _ j)) :=
  rfl

/-- The input string of one round of the finalization: `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩`, with the
final state `s`, the adversary's output `a` and the outer log `L` of the finalization so far. -/
def finInput (n : ℕ) (z ω s a L : List Bool) : List Bool :=
  pairEncode (seedIn n z ω) (pairEncode s (pairEncode a L))

/-- The input string of one round of the finalization is `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩`:
`finInput n z ω s a L = pairEncode (seedIn n z ω) (pairEncode s (pairEncode a L))`. -/
theorem finInput_eq (n : ℕ) (z ω s a L : List Bool) :
    finInput n z ω s a L = pairEncode (seedIn n z ω) (pairEncode s (pairEncode a L)) :=
  rfl

/-- **The finalization** in the final state `s`, after the adversary's output `a`: the
reduction's `outLen(n)`-bit output, computed with at most `finCall(n)` outer queries, in at most
`finCall(n) + 1` rounds of `finRun`. A malformed round output is the all-`false` output
(`decodeBitMove`'s default), and so is a further query after the budget is spent (a return at
zero remaining budget is accepted). -/
def finish (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool) : OracleComp (bitSpecAt din' dout' n) (Fin (H.outLen.eval n) → Bool) :=
  buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
      (H.outLen.eval n)
      (H.finRun (finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
        ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))
    (zeroBits _) (H.finCall.eval n) []

/-- The finalization is `buildComp` of its rounds, from the empty outer log, with budget
`finCall(n)` and the all-`false` output on a query after it is spent: `H.finish n z ω s a =
buildComp (fun L => decodeBitMove _ _ _ (H.finRun (finInput … L))) (zeroBits _)
(H.finCall.eval n) []`. -/
theorem finish_eq (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool) :
    H.finish n z ω s a =
      buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
          (H.outLen.eval n)
          (H.finRun (finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
            ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))
        (zeroBits _) (H.finCall.eval n) [] :=
  rfl

end InteractiveHandler

/-- **T2 (the efficiency fill's target; interactive handlers).** For a machine adversary `A`
with query budget `q` and `dα`-bit outputs against `k` bit-string oracles, and an interactive
handler `H` answering them through `k'` outer oracles, there is an oracle machine `B` against the
outer oracles, with budget `q(n) · perCall(n) + finCall(n)`, and at every parameter a bijection
`φ` from (`H`'s seed, `A`'s coins) to `B`'s coins, with the following property. `B` on input `z`
with coins `φ (ω, r)` is, as an oracle computation, exactly the reduction: `A` run on the input
`H.advInput n z ω`, its queries answered by `H` (input `z`, seed `ω`) from `H`'s initial state,
followed by `H`'s finalization on the final state and `A`'s output.

**Proof sketch** (the fill's; route note §"T2", with the log replay).
1. `B`'s next-move function, on `⟨z, O⟩` (`O` its encoded outer log) with the seed `ω`, `A`'s coins
   `r` and the advice `⟨α_A, s₀⟩` (`s₀ = H.init n`, as in T1), is the activation loop
   `EffFill.iRaw`, which **replays** the whole reduction, one activation per round: a round of `A`
   opens a call (a query within budget) or the finalization (an output, or a query at budget `0`
   with the all-`false` output); a round of a call reruns `H.run` on
   `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`, its answer (or the joint default at budget `0`) appending
   the entry to `A`'s log; a round of the finalization reruns `H.finRun`. An outer query within
   budget is answered by the next entry of `O`; when `O` is exhausted it is `B`'s next move, its
   canonical word (`EffFill.canonWord_eq`), and so is the finalization's output.
2. At most `2 + finCall(n) + q(n)(perCall(n) + 2)` rounds, with states of polynomial length
   (the unreplayed part of `O` is bounded by the input), so the raw function is polynomial-time
   (`EffFill.iRaw_poly`, from `GGMRed.stateLoopFun_poly`).
3. The reduction tree makes at most `q(n) · perCall(n) + finCall(n)` queries
   (`toCompOn_costBoundedBy`, `buildComp_costBoundedBy`, `EffFill.costBoundedBy_mul`,
   `simulate_costBoundedBy`, `CostBoundedBy.bind`), so `B`'s budget never cuts the replay short.
4. The functional equation (`EffFill.iRaw_spec`): `B`'s next-move function replays the reduction
   tree from the empty log (`EffFill.ReplaysFrom`), by induction along the phases
   (`EffFill.adv_phase`, `call_phase`, `fin_phase`) on every branch, since the outer answers are
   arbitrary; then `EffFill.buildComp_of_replaysFrom` gives the equality of trees. The handler's
   calls and finalization are read through `impl_apply`, `call_eq`, `input_eq`, `finish_eq` and
   `finInput_eq`.
5. Coins and advice as in T1 (`EffFill.exists_splitMachine`). -/
theorem exists_interactiveHandlerMachine (A : NUPPT) (q : PolyExpr)
    (din dout : Fin k → PolyExpr) (din' dout' : Fin k' → PolyExpr) (dα : PolyExpr)
    (H : InteractiveHandler k din dout k' din' dout') :
    ∃ B : NUPPT, ∀ n : ℕ, ∃ φ : (Fin (H.seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n,
      ∀ (z : List Bool) (ω : Fin (H.seedLen.eval n) → Bool) (r : A.Coins n),
        (simulate (H.impl n z ω)
            (A.toCompOn (bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n))
              n (q.eval n) (H.advInput n z ω) r) (H.init n)).bind
            (fun res => H.finish n z ω res.2 res.1) =
          B.toCompOn
            (bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) (H.outLen.eval n))
            n (q.eval n * H.perCall.eval n + H.finCall.eval n) z (φ (ω, r)) := by
  -- The machine: the replay loop of `EffFill.iRaw`, with `⟨A.advice n, s₀⟩` as advice and the
  -- seed passed as data.
  obtain ⟨B, hB⟩ := EffFill.exists_splitMachine A
    (EffFill.iRaw_poly A q dα din dout din' H.stateLen H.perCall H.outLen H.finCall dout' H.poly
      H.advIn_poly H.finRun_poly)
    (.add (.add (.mul (.const 2) A.adv) (.const 2)) H.stateLen)
    (fun n => pairEncode (A.advice n) (List.ofFn (H.init n))) (fun n => by
      rw [length_pairEncode, List.length_ofFn]
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
      have := A.advice_length n
      omega) H.seedLen
  refine ⟨B, fun n => ?_⟩
  obtain ⟨φ, hφ⟩ := hB n
  refine ⟨φ, fun z ω r => ?_⟩
  -- The handler's calls and finalization are the raw ones of `EffFill`.
  have himpl : H.impl n z ω =
      EffFill.iImpl din dout din' dout' H.stateLen H.perCall H.run n z (List.ofFn ω) := by
    funext i x s
    rw [InteractiveHandler.impl_apply, EffFill.iImpl_apply, InteractiveHandler.call_eq,
      EffFill.iCall_eq]
    simp only [InteractiveHandler.input_eq]
  have hfin : ∀ (s : Fin (H.stateLen.eval n) → Bool) (a : Fin (dα.eval n) → Bool),
      H.finish n z ω s a =
        EffFill.iFinish din' dout' H.stateLen H.outLen H.finCall H.finRun n z (List.ofFn ω) s a :=
            by
    intro s a
    rw [InteractiveHandler.finish_eq, EffFill.iFinish_eq]
    simp only [InteractiveHandler.finInput_eq, seedIn_eq]
  rw [himpl, InteractiveHandler.advInput_eq, seedIn_eq]
  simp only [hfin]
  rw [← EffFill.iRaw_spec A q dα din dout din' dout' H.stateLen H.perCall H.outLen H.finCall H.run
    H.advIn H.finRun n z (List.ofFn ω) r (H.init n), NUPPT.toCompOn_eq, bitCodec_timeout]
  congr 1
  funext O
  rw [bitCodec_decodeMove, hφ, EffFill.iX_eq]

/-! ### Companions: adversaries without input, and the bridge to pseudorandom functions (T4) -/

/-- **A machine without input is a machine with an input that it ignores.** For every machine
`A` there is a machine `A'` with the same coins whose computation on any input `x` is `A`'s
computation, for every codec and budget, the coins related by a bijection `φ`. So T1 and T2,
stated for adversaries with input, cover adversaries without one.

**Proof sketch.** `A'` is `NUPPT.exists_comp` of `A` with `pre = pairSndD` and `post = id`, so
`A'.coins = A.coins` and `A'.runAtL n ⟨x, L⟩ r = A.runAtL n L r` (`pairSndD_pairEncode`). The
bijection `φ` is `NUPPT.coinsCongr`, which transports the coins along the equal coin polynomials
and keeps the coin string (`NUPPT.runAt_coinsCongr`); with `runAt_eq` the next-move functions of
`A'.toCompOn codec n q x (φ r)` and `A.toComp codec n q r` agree on every log, and
`toCompOn_eq`, `toComp_eq` conclude. -/
theorem exists_toCompOn_of_toComp (A : NUPPT) :
    ∃ A' : NUPPT, A'.coins = A.coins ∧ ∀ n : ℕ, ∃ φ : A.Coins n ≃ A'.Coins n,
      ∀ {ι α : Type} {spec : OracleSpec ι} (codec : MachineCodec spec α) (q : ℕ)
        (x : List Bool) (r : A.Coins n),
        A'.toCompOn codec n q x (φ r) = A.toComp codec n q r := by
  obtain ⟨A', hc, -, -, hA'⟩ :=
    NUPPT.exists_comp A polyTimeComputable_pairSndD polyTimeComputable_id
  refine ⟨A', hc, fun n => ⟨NUPPT.coinsCongr hc.symm n, ?_⟩⟩
  intro ι α spec codec q x r
  have hnext : (fun hist => codec.decodeMove
      (A'.runAt n (pairEncode x (codec.encodeLog hist)) (NUPPT.coinsCongr hc.symm n r))) =
      fun hist => codec.decodeMove (A.runAt n (codec.encodeLog hist) r) := by
    funext hist
    rw [NUPPT.runAt_coinsCongr, hA', pairSndD_pairEncode, id_eq, ← NUPPT.runAt_eq]
  rw [NUPPT.toCompOn_eq, NUPPT.toComp_eq, hnext]

/-- **T4 (the efficiency fill's target; the bridge to pseudorandom functions).** An oracle
machine `B` against one `bitCodec` oracle (`ℓ₁(n)`-bit queries, `ℓ₂(n)`-bit answers) with a
one-bit output, run on the empty input, is a next-query machine of the ch. 2–4 layer: there is a
machine `B'` with the same coins whose oracle adversary `B'.toOracleAdversary`, run against any
`f`, returns the bit of `B`'s computation evaluated with `f`, the coins related by a bijection
`φ`. So `OracleEnsemble.Indist`, and with it `PRF`, applies to the machines of T2 with one outer
oracle and a one-bit output (through `oracleDist_apply` and `Bridge.eval_eq_evalFn`).

**Proof sketch.**
1. `B'` is `NUPPT.exists_comp` of `B` with two polynomial-time translators, so `B'.coins = B.coins`:
   - `EffFill.bridgePre` maps the history `⟨⟨x₁, y₁⟩, ⟨…, []⟩⟩` (`encodeHist`) to
     `⟨[], ⟨⟨[], ⟨x₁, y₁⟩⟩, ⟨…, []⟩⟩⟩`, `B`'s empty input and its log (`bitCodec_encodeEntry` with
     `1^0 = []`), by emitting one piece per suffix (`Complexity.polyTimeComputable_iterateEmit` with
     the step `pairSndD`; `EffFill.bridgePre_encodeHist`);
   - `EffFill.bridgePost` maps a canonical query word `⟨[false], ⟨[], x⟩⟩` (tested by re-encoding)
     to `⟨[false], x⟩`, the word `⟨[true], [true]⟩` to the verdict `[true, true]`, and every other
     word to `[true, false]`; then `decodeOracleMove` and `decodeBitMove` read corresponding moves
     (`EffFill.bridgePost_spec`, from `decodeBitMove_query`, `decodeBitMove_ret`,
     `decodeBitMove_of_not_canonical` and the case lemmas of `decodeOracleMove`), a payload of the
     wrong length included.
2. Both trees branch on corresponding moves, so by induction on the budget
   (`EffFill.eval_buildTree_bridge`: `buildTree`'s and `buildComp`'s case lemmas) their
   evaluations against `f` and `fun _ => f` agree (`QueryTree.eval_query`,
   `OracleComp.evalFn_query`); at the timeout the verdict `false` is bit `0` of `zeroBits 1`
   (`zeroBits_apply`). `toOracleAdversary_eq` and `toCompOn_eq` unfold the two sides.
3. `φ` is `NUPPT.coinsCongr`, as in `exists_toCompOn_of_toComp`. -/
theorem exists_toOracleAdversary_of_bitCodec (B : NUPPT) (ℓ₁ ℓ₂ : PolyExpr) :
    ∃ B' : NUPPT, B'.coins = B.coins ∧ ∀ n : ℕ, ∃ φ : B.Coins n ≃ B'.Coins n,
      ∀ (q : ℕ) (r : B.Coins n) (f : (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)),
        (B'.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) q (φ r)).eval f =
          (B.toCompOn (bitCodec (fun _ : Fin 1 => ℓ₁.eval n) (fun _ => ℓ₂.eval n) 1) n q []
              r).evalFn (fun _ => f) 0 := by
  obtain ⟨B', hc, -, -, hB'⟩ :=
    NUPPT.exists_comp B EffFill.bridgePre_poly EffFill.bridgePost_poly
  refine ⟨B', hc, fun n => ⟨NUPPT.coinsCongr hc.symm n, fun q r f => ?_⟩⟩
  have hnext : (fun hist : List ((Fin (ℓ₁.eval n) → Bool) × (Fin (ℓ₂.eval n) → Bool)) =>
      decodeOracleMove (ℓ₁.eval n)
      (B'.runAt n (encodeHist hist) (NUPPT.coinsCongr hc.symm n r))) =
      fun hist => decodeOracleMove (ℓ₁.eval n)
        (EffFill.bridgePost (B.runAt n (EffFill.bridgePre (encodeHist hist)) r)) := by
    funext hist
    rw [NUPPT.runAt_coinsCongr, hB', ← NUPPT.runAt_eq]
  have h := EffFill.eval_buildTree_bridge (ℓ₁.eval n) (ℓ₂.eval n) (fun y => B.runAt n y r) f q []
  rw [EffFill.logHist_eq, List.map_nil] at h
  rw [NUPPT.toOracleAdversary_eq, hnext, NUPPT.toCompOn_eq]
  simp only [bitCodec_decodeMove, bitCodec_timeout]
  exact h

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Encryption/PublicKey/EnsembleSecurity.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import TCSlib.Cryptography.Encryption.PublicKey.Scheme
import TCSlib.Cryptography.Encryption.PublicKey.Hybrid

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Ensemble security for public-key encryption

The experiments expose the public key with the ciphertexts. In the fixed-vector
experiment, all encryptions share one key and use independent encryption coins.

The scheme interface gives decryption the secret key and ciphertext. A scheme
that needs `1^n` for decryption includes it in the secret key.

## Main definitions

* `TCSlib.Cryptography.PublicKeyScheme.pkEncDist` and `PublicKeyScheme.Secure` give the
  single-message experiment and security predicate.
* `TCSlib.Cryptography.PublicKeyScheme.pkMultiEncDist` and
  `PublicKeyScheme.MultiMessageSecure` give the fixed-vector experiment and security predicate.
* `TCSlib.Cryptography.BitPublicKeyScheme.pkEncDist` and `BitPublicKeyScheme.SingleBitSecure`
  specialize the experiment to one bit. `BitPublicKeyScheme.bitwise` encrypts a string bit by bit.
* `TCSlib.Cryptography.hybridPlant` inserts a challenge ciphertext at the selected position
  and encrypts the other messages with the public key.

## Main results

* `TCSlib.Cryptography.distAdv_multi_le_sum` bounds the fixed-vector advantage by the sum
  of the single-position advantages.
* `TCSlib.Cryptography.PublicKeyScheme.Secure.multiMessageSecure` lifts single-message
  security to fixed-vector security.
* `TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.bitwise` proves security of
  the bitwise scheme. `BitPublicKeyScheme.singleBitSecure_iff` characterizes single-bit
  security by the negligible advantage between the two possible messages.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 102.2 and p. 103.)
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset
open PrivateKeyScheme (encodeList)

/-! ## Ensemble security [PS10, Definition 102.2] -/

namespace PublicKeyScheme

/-- The distribution `{(pk, sk) ← Gen(1^n) : ⟨pk, Enc_pk(m)⟩}` of [PS10, Definition 102.2] as a
sampler from the coins of `Gen` and `Enc`. -/
def pkEncDist (S : PublicKeyScheme) (n : ℕ) (m : Fin n → Bool) :
    S.gen.Coins n × S.enc.Coins n → List Bool :=
  fun r => pairEncode (pairFstD (S.gen.runAt n [] r.1))
    (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] r.1)) (List.ofFn m)) r.2)

/-- **Secure public-key encryption** [PS10, Definition 102.2]: for every non-uniform PPT `D`
there is a negligible `ε` such that for all `n` and `m₀, m₁ ∈ {0,1}^n`, `D` distinguishes
`⟨pk, Enc_pk(m₀)⟩` from `⟨pk, Enc_pk(m₁)⟩` with advantage at most `ε(n)`.

**Deviation:** `D` receives `1^n` with its sample (D5). -/
def Secure (S : PublicKeyScheme) : Prop :=
  ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (m₀ m₁ : Fin n → Bool),
    distAdv (S.pkEncDist n m₀) (S.pkEncDist n m₁) (D.distinguisherL n) ≤ ε n

end PublicKeyScheme

namespace PublicKeyScheme

/-- The distribution `{(pk, sk) ← Gen(1^n) : ⟨pk, ⟨Enc_pk(m₀), …, Enc_pk(m_q)⟩⟩}` of the
multi-message security notion for public-key encryption [PS10, p. 103]: `q + 1` encryptions
under one public key with independent encryption coins. -/
def pkMultiEncDist (S : PublicKeyScheme) (n q : ℕ) (m : Fin (q + 1) → Fin n → Bool) :
    S.gen.Coins n × (Fin (q + 1) → S.enc.Coins n) → List Bool :=
  fun r => pairEncode (pairFstD (S.gen.runAt n [] r.1)) (encodeList (List.ofFn fun i =>
    S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] r.1)) (List.ofFn (m i))) (r.2 i)))

/-- **Multi-message secure public-key encryption** [PS10, p. 103, "we can extend the
definition to multi-message security", i.e. Definition 93.1 with a public key]: for every
non-uniform PPT `D` and polynomial `q` there is a negligible `ε` such that for all `n` and all
message vectors `m, m' ∈ ({0,1}^n)^{q(n)+1}`, `D` distinguishes the encryptions of `m` from
those of `m'` under one key pair with advantage at most `ε(n)` (the public key is part of the
sample).

**Deviation:** `D` receives `1^n`; the ciphertexts are nested pairs. -/
def MultiMessageSecure (S : PublicKeyScheme) : Prop :=
  ∀ (D : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n (m m' : Fin (q.eval n + 1) → Fin n → Bool),
      distAdv (S.pkMultiEncDist n (q.eval n) m) (S.pkMultiEncDist n (q.eval n) m')
        (D.distinguisherL n) ≤ ε n

end PublicKeyScheme

/-! ## The shared-key hybrid lemma (Thm-103.d, concrete) -/

/-- The `j`-th hybrid distinguisher of the single ⇒ multi-message argument
[PS10, p. 103, "the key point here is that we can efficiently generate encryptions of any
message, without knowing the secret key"]: on a sample `⟨pk, c⟩` it encrypts `m'_0, …, m'_{j-1}`
and `m_{j+1}, …, m_q` itself under `pk` with its own coins `r.1`, plants `c` at position `j`
and runs `D` with coins `r.2`. -/
def hybridPlant {π μ γ ρ ρ' : Type*} {q : ℕ} (E : π → μ → ρ → γ) (m m' : Fin (q + 1) → μ)
    (j : Fin (q + 1)) (D : π × (Fin (q + 1) → γ) → ρ' → Bool) :
    π × γ → (Fin (q + 1) → ρ) × ρ' → Bool :=
  fun pc r => D (pc.1, fun i =>
    if i < j then E pc.1 (m' i) (r.1 i) else if i = j then pc.2 else E pc.1 (m i) (r.1 i)) r.2

/-- **The hybrid bound with a shared public parameter** (the concrete content of the single ⇒
multi-message theorem for public-key encryption [PS10, p. 103] and of the multi-value hiding of
commitments [PS10, Theorem 126.4, "show this!"]): for a parameter sampler `P` (the public key
from `Gen`'s coins), an encryptor `E pk m r`, message vectors `m, m'` and any `D`, the advantage
of `D` between the `q + 1` encryptions of `m` and of `m'` under one `pk` is at most the sum over
`j` of the advantages of `hybridPlant E m m' j D` between the single encryptions of `m_j` and
`m'_j`. (Unlike `exists_multicopyRed_ge` the copies share the parameter `pk` and the samplers
depend on the position.)

**Proof sketch.** Hybrids `H_j := ⟨pk, (E pk m'_i r_i)_{i<j}, (E pk m_i r_i)_{i≥j}⟩` on the seeds
`κ × (Fin (q+1) → ρ)`, `H_0` and `H_{q+1}` the two sides; `abs_sub_le_sum_hybrids` over
`j ∈ range (q+1)` (`Fin.sum_univ_eq_sum_range`). Each gap `|Pr[D(H_j)] − Pr[D(H_{j+1})]|` equals
the advantage of `hybridPlant E m m' j D` between `⟨pk, E pk m_j r⟩` and `⟨pk, E pk m'_j r⟩`:
`acceptProb (⟨pk, E pk m_j r⟩) (hybridPlant …)` is the probability over `(k, r), (v, r')` of
`D ⟨P k, plant_j (E (P k) m_j r) v⟩ r'`, in which the coordinate `v j` is unused; replacing
`v` by `update v j r` (`OneWay.uprob_update`, `[Nonempty ρ]`) and regrouping the seeds
(`uprob_comp_equiv`) gives `Pr[D(H_j)]`, and likewise `m'_j` gives `Pr[D(H_{j+1})]`
(`Function.update_apply`, the `if` cases `i < j`, `i = j`, `i > j`). -/
theorem distAdv_multi_le_sum {κ π μ γ ρ ρ' : Type*} [Fintype κ] [Fintype ρ] [Fintype ρ']
    [Nonempty ρ] {q : ℕ} (P : κ → π) (E : π → μ → ρ → γ) (m m' : Fin (q + 1) → μ)
    (D : π × (Fin (q + 1) → γ) → ρ' → Bool) :
    distAdv (fun z : κ × (Fin (q + 1) → ρ) => (P z.1, fun i => E (P z.1) (m i) (z.2 i)))
      (fun z : κ × (Fin (q + 1) → ρ) => (P z.1, fun i => E (P z.1) (m' i) (z.2 i))) D ≤
    ∑ j : Fin (q + 1), distAdv (fun z : κ × ρ => (P z.1, E (P z.1) (m j) z.2))
      (fun z : κ × ρ => (P z.1, E (P z.1) (m' j) z.2)) (hybridPlant E m m' j D) :=
  distAdv_tuple_le_sum P E m m' D

/-! ## Single-bit security and the bitwise scheme [PS10, p. 103] -/

namespace BitPublicKeyScheme

/-- The distribution `{(pk, sk) ← Gen(1^n) : ⟨pk, Enc_pk(b)⟩}` of a single-bit scheme. -/
def pkEncDist (S : BitPublicKeyScheme) (n : ℕ) (b : Bool) :
    S.gen.Coins n × S.enc.Coins n → List Bool :=
  fun r => pairEncode (pairFstD (S.gen.runAt n [] r.1))
    (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] r.1)) [b]) r.2)

/-- The single-bit sampler returns the public key and the encryption of `[b]`
on the supplied key-generation and encryption coins. -/
theorem pkEncDist_eq (S : BitPublicKeyScheme) (n : ℕ) (b : Bool)
    (r : S.gen.Coins n × S.enc.Coins n) :
    S.pkEncDist n b r = pairEncode (pairFstD (S.gen.runAt n [] r.1))
      (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] r.1)) [b]) r.2) := rfl

/-- **Single-bit security** [PS10, p. 103, "we only require that encryptions of 0 and 1 are
indistinguishable"]: Definition 102.2 with message space `{0,1}`: for every non-uniform PPT `D`
there is a negligible `ε` with, for all `n` and `b₀, b₁ ∈ {0,1}`, advantage at most `ε(n)`
between `⟨pk, Enc_pk(b₀)⟩` and `⟨pk, Enc_pk(b₁)⟩`. -/
def SingleBitSecure (S : BitPublicKeyScheme) : Prop :=
  ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (b₀ b₁ : Bool),
    distAdv (S.pkEncDist n b₀) (S.pkEncDist n b₁) (D.distinguisherL n) ≤ ε n

/-- **Single-bit security is the negligibility of the `0`-versus-`1` advantage** (the only
nontrivial pair of messages; sanity for the quantifier form of the definition).

**Proof sketch.** `→`: specialize to `(false, true)` and `Negligible.mono` (the advantage is
nonnegative). `←`: take `ε n` to be the `(false, true)` advantage itself; the pairs `(b, b)` have
advantage `0` and `(true, false)` the same advantage (`abs_sub_comm`). -/
theorem singleBitSecure_iff (S : BitPublicKeyScheme) : S.SingleBitSecure ↔
    ∀ D : NUPPT, Negligible fun n =>
      distAdv (S.pkEncDist n false) (S.pkEncDist n true) (D.distinguisherL n) := by
  constructor
  · intro h D
    obtain ⟨ε, hε, hle⟩ := h D
    refine hε.mono ⟨0, fun n _ => ?_⟩
    have h0 : 0 ≤ distAdv (S.pkEncDist n false) (S.pkEncDist n true) (D.distinguisherL n) :=
      abs_nonneg _
    rw [abs_of_nonneg h0]
    exact (hle n false true).trans (le_abs_self _)
  · intro h D
    refine ⟨_, h D, fun n b₀ b₁ => ?_⟩
    cases b₀ <;> cases b₁
    · simp only [distAdv_def, sub_self, abs_zero]; exact abs_nonneg _
    · exact le_rfl
    · exact (abs_sub_comm _ _).le
    · simp only [distAdv_def, sub_self, abs_zero]; exact abs_nonneg _

/-- The raw encryptor of the bitwise scheme on the layout `⟨⟨⟨1^n, ⟨pk, m⟩⟩, []⟩, r⟩`: the block
encryptor with one-bit blocks on the state `⟨1^n, ⟨pk, ⟨m, r⟩⟩⟩`. -/
def bitwiseEncFun (S : BitPublicKeyScheme) (z : List Bool) : List Bool :=
  blockEncFun S.enc.output (.const 1) S.enc.coins
    (blockState (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)) (pairSndD (NUPPT.inArg z))
      (NUPPT.inCoins z))

/-- The raw encryptor of the bitwise scheme is polynomial-time. -/
theorem bitwiseEncFun_poly (S : BitPublicKeyScheme) : PolyTimeComputable S.bitwiseEncFun :=
  (blockEncFun_poly S.enc.polyTimeComputable_output _ _).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode
      ((polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg).pairEncode
        ((polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg).pairEncode
          NUPPT.polyTimeComputable_inCoins)))

/-- A string of the right length is the encoding of a typed string. -/
private theorem exists_ofFn_eq {ℓ : ℕ} (w : List Bool) (h : w.length = ℓ) :
    ∃ x : Fin ℓ → Bool, List.ofFn x = w := by
  subst h
  exact ⟨fun j => w.get j, List.ofFn_get w⟩

/-- A `flatMap` of singletons indexed by `Fin n` is the string. -/
private theorem flatMap_ofFn_singleton {n : ℕ} (f : Fin n → List Bool) (g : List Bool → List Bool)
    (m : Fin n → Bool) (h : ∀ i, g (f i) = [m i]) :
    (List.ofFn f).flatMap g = List.ofFn m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.flatMap_cons, h, ih (fun i => f i.succ) (fun i => m i.succ)
      (fun i => h i.succ)]
    rfl

/-- **Unfolding of the bitwise encryptor**: `Enc'(1^n, ⟨pk, m⟩; r)` is the tuple of the `n`
single-bit encryptions `Enc(1^n, ⟨pk, [m_i]⟩; r_i)` with the consecutive `B(n)`-coin segments
`r_i` of `r` (`blockEncFun_spec`, `blockList_ofFn`, `Uniform.runAtL_eq`). -/
theorem bitwise_enc_runAtL (S : BitPublicKeyScheme) (n : ℕ) (pk : List Bool) (m : Fin n → Bool)
    (r : List Bool) :
    (NUPPT.ofPolyTimeUniform S.bitwiseEncFun_poly (.mul .var S.enc.coins)).runAtL n
        (pairEncode pk (List.ofFn m)) r =
      encodeList (List.ofFn fun i : Fin n =>
        S.enc.runAtL n (pairEncode pk [m i]) (coinBlock (S.enc.coinLen n) i r)) := by
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp only [bitwiseEncFun, NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq,
    pairFstD_pairEncode, pairSndD_pairEncode, blockEncFun_eq]
  rw [blockEncFun_spec S.enc.output (.const 1) S.enc.coins (List.replicate n true) pk
    _ (List.ofFn m) r (by
      simp only [blockState_eq, length_pairEncode, List.length_ofFn, PolyExpr.eval_const, mul_one]
      omega)]
  simp only [PolyExpr.eval_const, List.length_replicate]
  rw [blockList_ofFn S.enc.output _ _ _ n m r _ (by
    simp only [blockState_eq, length_pairEncode, List.length_ofFn]; omega)]
  congr 1
  refine congrArg List.ofFn (funext fun i => ?_)
  rw [S.enc_uniform.runAtL_eq]
  rfl

/-- **Unfolding of the bitwise encryptor**, typed coins: `Enc'(1^n, ⟨pk, m⟩; r)` is the tuple of
the single-bit encryptions with the consecutive `B(n)`-coin segments of `List.ofFn r`. -/
theorem bitwise_enc_runAt (S : BitPublicKeyScheme) (n : ℕ) (pk : List Bool) (m : Fin n → Bool)
    (r : (NUPPT.ofPolyTimeUniform S.bitwiseEncFun_poly (.mul .var S.enc.coins)).Coins n) :
    (NUPPT.ofPolyTimeUniform S.bitwiseEncFun_poly (.mul .var S.enc.coins)).runAt n
        (pairEncode pk (List.ofFn m)) r =
      encodeList (List.ofFn fun i : Fin n =>
        S.enc.runAtL n (pairEncode pk [m i]) (coinBlock (S.enc.coinLen n) i (List.ofFn r))) := by
  rw [NUPPT.runAt_eq, bitwise_enc_runAtL]

/-- **The bitwise scheme** [PS10, p. 103, "simply encrypting each bit of the message using the
single-bit secure encryption"]: the same key generator, `Enc'_pk(m) = ⟨Enc_pk(m_1), …, Enc_pk(m_n)⟩`
with `n · B(n)` coins (`blockEncFun`, one-bit blocks), `Dec'_sk(c) = Dec_sk(c_1) ‖ ⋯ ‖ Dec_sk(c_n)`
(`decListFun`), decoded as an `n`-bit string.

**Deviation:** the text's "`Dec` returns `⊥` if any bit decrypts to `⊥`" is realised only up
to the output-length convention of D5 (an honest ciphertext decrypts correctly; a malformed one
decrypts to a wrong-length string or to an arbitrary `n`-bit string). -/
noncomputable def bitwise (S : BitPublicKeyScheme) : PublicKeyScheme where
  gen := S.gen
  enc := NUPPT.ofPolyTimeUniform S.bitwiseEncFun_poly (.mul .var S.enc.coins)
  dec := decListFun S.dec
  gen_uniform := S.gen_uniform
  enc_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  dec_poly := decListFun_poly S.dec_poly
  correct := by
    intro n m rg re
    rw [bitwise_enc_runAt, decListFun_eq,
      decListFun_spec S.dec _ _ _ (by
        refine (length_le_length_encodeList _).trans ?_
        simp only [length_pairEncode]
        omega)]
    rw [flatMap_ofFn_singleton _ _ m (fun i => ?_)]
    · exact decodeFin_ofFn m
    · have hre : (List.ofFn re).length = n * S.enc.coins.eval n := by
        rw [← NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn S.bitwiseEncFun_poly (.mul .var S.enc.coins)
          n re, List.length_ofFn, PolyExpr.eval_mul, PolyExpr.eval_var]
      have hlen : (coinBlock (S.enc.coinLen n) i (List.ofFn re)).length = S.enc.coinLen n := by
        simp only [coinBlock_eq, List.length_take, List.length_drop]
        rw [hre, NUPPT.coinLen_eq]
        have hi : (i : ℕ) + 1 ≤ n := i.isLt
        have := Nat.mul_le_mul_right (S.enc.coins.eval n) hi
        rw [Nat.add_mul, one_mul] at this
        omega
      obtain ⟨re', hre'⟩ := exists_ofFn_eq _ hlen
      have := S.correct n (m i) rg re'
      rw [NUPPT.runAt_eq (A := S.enc), hre'] at this
      exact this

/-- The coin count of the bitwise encryptor: `n · B(n)`. -/
theorem bitwise_enc_coinLen (S : BitPublicKeyScheme) (n : ℕ) :
    n * S.enc.coinLen n = (PolyExpr.mul .var S.enc.coins).eval n := by
  rw [NUPPT.coinLen_eq, PolyExpr.eval_mul, PolyExpr.eval_var]

/-- **The coins of the bitwise encryptor are `n` single-bit coin blocks**: the published
equivalence `(Fin n → {0,1}^{B(n)}) ≃ S.bitwise.enc.Coins n` (`coinBlocks`, then `finCongr` along
`bitwise_enc_coinLen` and the coin equivalence of `ofPolyTimeUniform`). -/
noncomputable def bitwiseEncCoins (S : BitPublicKeyScheme) (n : ℕ) :
    (Fin n → S.enc.Coins n) ≃ S.bitwise.enc.Coins n :=
  (coinBlocks n (S.enc.coinLen n)).trans
    ((Equiv.arrowCongr (finCongr (S.bitwise_enc_coinLen n)) (Equiv.refl Bool)).trans
      (NUPPT.coinsEquiv_ofPolyTimeUniform S.bitwiseEncFun_poly (.mul .var S.enc.coins) n).symm)

/-- The bitwise encryptor's coin string on the blocks `v` is that of `coinBlocks n B v`. -/
theorem bitwiseEncCoins_ofFn (S : BitPublicKeyScheme) (n : ℕ) (v : Fin n → S.enc.Coins n) :
    List.ofFn (S.bitwiseEncCoins n v) = List.ofFn (coinBlocks n (S.enc.coinLen n) v) := by
  have key : ∀ w, List.ofFn ((NUPPT.coinsEquiv_ofPolyTimeUniform S.bitwiseEncFun_poly
      (.mul .var S.enc.coins) n).symm w) = List.ofFn w := fun w => by
    rw [← NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn, Equiv.apply_symm_apply]
  unfold bitwiseEncCoins
  rw [Equiv.trans_apply, Equiv.trans_apply]
  exact (key _).trans (List.ofFn_congr (S.bitwise_enc_coinLen n) _).symm

/-- The single-bit sampler is `singleDist` on the one-bit message `[b]`. -/
private theorem pkEncDist_eq_singleDist (S : BitPublicKeyScheme) (n : ℕ) (b : Bool) :
    S.pkEncDist n b = singleDist S.gen S.enc n 1 (fun _ => b) := by
  funext r
  simp only [BitPublicKeyScheme.pkEncDist, singleDist_def, ofFn_fin_one]

/-- The ciphertext of the bitwise scheme on the coin blocks `v` is the tuple of the single-bit
encryptions with coins `v_i` (`bitwise_enc_runAt`, `coinBlock_ofFn_coinBlocks`): the sampler
`S.bitwise.pkEncDist n m` read through `bitwiseEncCoins` is `multiDist` with one-bit blocks. -/
private theorem bitwise_pkEncDist_coinBlocks (S : BitPublicKeyScheme) (n : ℕ) (m : Fin n → Bool)
    (r : S.gen.Coins n) (v : Fin n → S.enc.Coins n) :
    S.bitwise.pkEncDist n m (r, S.bitwiseEncCoins n v) =
      multiDist S.gen S.enc n n 1 (fun i _ => m i) (r, v) := by
  show pairEncode (pairFstD (S.gen.runAt n [] r))
      ((NUPPT.ofPolyTimeUniform S.bitwiseEncFun_poly (.mul .var S.enc.coins)).runAt n
        (pairEncode (pairFstD (S.gen.runAt n [] r)) (List.ofFn m)) (S.bitwiseEncCoins n v)) =
    _
  rw [bitwise_enc_runAt]
  simp only [multiDist_eq]
  refine congrArg _ (congrArg (fun l => encodeList (List.ofFn l)) (funext fun i => ?_))
  rw [bitwiseEncCoins_ofFn, coinBlock_ofFn_coinBlocks, ← NUPPT.runAt_eq, ofFn_fin_one]

/-- **The bitwise scheme's ciphertexts as a tuple of single-bit encryptions**: the acceptance
probability of any distinguisher on `S.bitwise.pkEncDist n m` is its acceptance probability on
`multiDist` with one-bit blocks (the coin bijection `coinBlocks`, `uprob_comp_equiv`). -/
private theorem acceptProb_bitwise_pkEncDist (S : BitPublicKeyScheme) (n : ℕ) (m : Fin n → Bool)
    {ρ : Type*} [Fintype ρ] (Dst : List Bool → ρ → Bool) :
    acceptProb (S.bitwise.pkEncDist n m) Dst =
      acceptProb (multiDist S.gen S.enc n n 1 (fun i _ => m i)) Dst := by
  rw [acceptProb_def, acceptProb_def]
  rw [← uprob_comp_equiv
    (((Equiv.refl (S.gen.Coins n)).prodCongr (S.bitwiseEncCoins n)).prodCongr
      (Equiv.refl ρ))]
  congr 1
  funext z
  obtain ⟨⟨r, v⟩, ρ'⟩ := z
  simp only [Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]
  rw [bitwise_pkEncDist_coinBlocks]

/-- **Bitwise encryption under a single-bit secure scheme is secure** [PS10, p. 103, "the security
of the new scheme follows directly from the multi-message security (which is equivalent to
traditional security) of the single-bit secure encryption scheme"].

**Proof sketch.** Fix a non-uniform PPT `D`. At each `n` choose `(m₀ⁿ, m₁ⁿ)` maximizing the
advantage of `D.distinguisherL n` between `pkEncDist n m₀` and `pkEncDist n m₁` of `S.bitwise`
(`Finset.exists_max_image`). By `bitwise_enc_runAtL` and the coin split
`(Fin (n · B n) → Bool) ≃ (Fin n → Fin (B n) → Bool)` (`FunFamily.blocks`, `coinBlock` of
`List.ofFn`; `acceptProb_comp_equiv`), the two samples are the shared-key tuples of
`distAdv_multi_le_sum` with `P := pk`, `E pk [b] r := Enc(1^n, ⟨pk, [b]⟩; r)`, `q := n − 1`
(for `n = 0` the advantage is `0`), after moving the string encoding into `D`
(`distAdv_comp`). Hence the advantage is at most `∑_{j<n}` of the advantages of
`hybridPlant E m₀ m₁ j D` between the single-bit encryptions of `m₀ⁿ_j` and `m₁ⁿ_j`, each at
most that of the machine `B_j`: advice `⟨⟨1^j, ⟨ofFn m₀ⁿ, ofFn m₁ⁿ⟩⟩, D.advice n⟩`
(`NUPPT.exists_withAdvice`), coins `var · S.enc.coins + D.coins` (`NUPPT.exists_split`), which
on `⟨pk, c⟩` encrypts the first `j` bits of `m₁ⁿ` and the last `n − j − 1` bits of `m₀ⁿ` with
`blockEncFun` (one-bit blocks, `blockEncFun_spec`), assembles the tuple
`encodeList l₁ ++ ⟨c, []⟩ ++ encodeList l₂` (`encodeList_eq_flatMap`, `pairEncode_nil_append`),
and runs `D` (`NUPPT.exists_comp`); by `singleBitSecure_iff` applied to `h` (and the `(b, b)` pairs
being `0`) each term is `≤ ε_j(n)`. Over a single machine `B` with the index `j` in the advice
(`Finset.exists_max_image` over `j`), the total is `≤ n · ε(n)`, negligible by
`Negligible.mul_pow`; the maximality of `(m₀ⁿ, m₁ⁿ)` gives the uniform bound. (Formally: `acceptProb_bitwise_pkEncDist`
reads the ciphertexts as `multiDist` with one-bit blocks, and `exists_hybridBound` with
`K := var`, `L := const 1` supplies the single machine `B` and the bound `n · ε(n)`.) -/
theorem SingleBitSecure.bitwise {S : BitPublicKeyScheme} (h : S.SingleBitSecure) :
    S.bitwise.Secure := by
  intro D
  -- the worst message pair at each parameter (hard-wired into the reduction)
  have hmax : ∀ n, ∃ p : (Fin n → Bool) × (Fin n → Bool), ∀ q : (Fin n → Bool) × (Fin n → Bool),
      distAdv (S.bitwise.pkEncDist n q.1) (S.bitwise.pkEncDist n q.2) (D.distinguisherL n) ≤
        distAdv (S.bitwise.pkEncDist n p.1) (S.bitwise.pkEncDist n p.2) (D.distinguisherL n) := by
    intro n
    obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ
      (fun q : (Fin n → Bool) × (Fin n → Bool) =>
        distAdv (S.bitwise.pkEncDist n q.1) (S.bitwise.pkEncDist n q.2) (D.distinguisherL n))
      Finset.univ_nonempty
    exact ⟨p, fun q => hp q (Finset.mem_univ q)⟩
  choose μ hμ using hmax
  -- the hybrid machine for the worst pairs: `n` positions, one-bit blocks
  obtain ⟨B, hB⟩ := exists_hybridBound S.gen S.enc D S.enc_uniform .var (.const 1)
    (fun n i _ => (μ n).1 i) (fun n i _ => (μ n).2 i)
  obtain ⟨ε, hε, hBε⟩ := h B
  refine ⟨fun n => (n : ℝ) * ε n, EnsembleLemmas.negligible_polyExpr_mul .var hε, fun n m₀ m₁ => ?_⟩
  refine (hμ n (m₀, m₁)).trans ?_
  have hε0 : 0 ≤ ε n := (abs_nonneg _).trans ((distAdv_def _ _ _).symm.trans_le (hBε n false false))
  have hsingle : ∀ msg msg' : Fin 1 → Bool,
      distAdv (singleDist S.gen S.enc n 1 msg) (singleDist S.gen S.enc n 1 msg')
        (B.distinguisherL n) ≤ ε n := by
    intro msg msg'
    have h1 : msg = fun _ => msg 0 := funext fun i => congrArg msg (Subsingleton.elim i 0)
    have h2 : msg' = fun _ => msg' 0 := funext fun i => congrArg msg' (Subsingleton.elim i 0)
    rw [h1, h2, ← S.pkEncDist_eq_singleDist, ← S.pkEncDist_eq_singleDist]
    exact hBε n _ _
  have hn := hB n (ε n) hε0 hsingle
  rw [distAdv_def] at hn ⊢
  rw [acceptProb_bitwise_pkEncDist, acceptProb_bitwise_pkEncDist]
  exact hn

end BitPublicKeyScheme

/-! ## Single ⇒ multi-message security for public-key encryption [PS10, p. 103] -/

/-- **For public-key encryption, single-message security implies multi-message security**
[PS10, p. 103, "multi-message security is equivalent to single-message security … We leave it as
an exercise to the reader"].

**Proof sketch.** Fix `D` and `q`. At each `n` choose `(mⁿ, m'ⁿ)` maximizing the advantage of
`D.distinguisherL n` between `pkMultiEncDist n (q n) m` and `pkMultiEncDist n (q n) m'`
(`Finset.exists_max_image`). The samples are the shared-key tuples of `distAdv_multi_le_sum`
with `P := pk ∘ Gen`, `E pk m r := Enc(1^n, ⟨pk, m⟩; r)` after moving the tuple encoding into `D`
(`distAdv_comp`), so the advantage is at most `∑_{j ≤ q n}` of the advantages of
`hybridPlant E mⁿ m'ⁿ j D` between `pkEncDist n (mⁿ_j)` and `pkEncDist n (m'ⁿ_j)`. Each is the
advantage of the machine `B_j`: advice `⟨⟨1^j, ⟨ofFn mⁿ, ofFn m'ⁿ⟩⟩, D.advice n⟩`
(`NUPPT.exists_withAdvice`, bound `2(q+1)·var + …`), coins `q · S.enc.coins + D.coins`
(`NUPPT.exists_split`), which on `⟨pk, c⟩` encrypts the other `q n` messages with
`blockEncFun` (`n`-bit blocks, `blockEncFun_spec`), plants `c` at position `j`
(`encodeList_eq_flatMap`, `pairEncode_nil_append`) and runs `D` (`NUPPT.exists_comp`); by `h`
each term is `≤ ε(n)` for the single machine `B` with the index `j` in its advice (take the
maximizing `j` per `n`), so the total is `≤ (q n + 1) ε(n)`, negligible by `Negligible.mul_pow`
and `PolyExpr.eval_le`; maximality of `(mⁿ, m'ⁿ)` gives the uniform bound. (Formally:
`exists_hybridBound` with `K := q + 1`, `L := var` on the samplers `singleDist`/`multiDist`,
which are `pkEncDist`/`pkMultiEncDist` definitionally.) -/
theorem PublicKeyScheme.Secure.multiMessageSecure {S : PublicKeyScheme} (h : S.Secure) :
    S.MultiMessageSecure := by
  intro D q
  -- the worst pair of message vectors at each parameter (hard-wired into the reduction)
  have hmax : ∀ n, ∃ p : (Fin (q.eval n + 1) → Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool),
      ∀ p' : (Fin (q.eval n + 1) → Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool),
        distAdv (S.pkMultiEncDist n (q.eval n) p'.1) (S.pkMultiEncDist n (q.eval n) p'.2)
            (D.distinguisherL n) ≤
          distAdv (S.pkMultiEncDist n (q.eval n) p.1) (S.pkMultiEncDist n (q.eval n) p.2)
            (D.distinguisherL n) := by
    intro n
    obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ
      (fun p' : (Fin (q.eval n + 1) → Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool) =>
        distAdv (S.pkMultiEncDist n (q.eval n) p'.1) (S.pkMultiEncDist n (q.eval n) p'.2)
          (D.distinguisherL n))
      Finset.univ_nonempty
    exact ⟨p, fun p' => hp p' (Finset.mem_univ p')⟩
  choose μ hμ using hmax
  -- the hybrid machine for the worst pairs: `q + 1` positions, `n`-bit blocks
  obtain ⟨B, hB⟩ := exists_hybridBound S.gen S.enc D S.enc_uniform (.add q (.const 1)) .var
    (fun n => (μ n).1) (fun n => (μ n).2)
  obtain ⟨ε, hε, hBε⟩ := h B
  refine ⟨fun n => (((PolyExpr.add q (.const 1)).eval n : ℕ) : ℝ) * ε n,
    EnsembleLemmas.negligible_polyExpr_mul _ hε, fun n m m' => ?_⟩
  refine (hμ n (m, m')).trans ?_
  have hε0 : 0 ≤ ε n := (abs_nonneg _).trans (hBε n (fun _ => false) (fun _ => false))
  exact hB n (ε n) hε0 fun msg msg' => hBε n msg msg'

end TCSlib.Cryptography
