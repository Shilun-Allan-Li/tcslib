## ===== briefs/pass-shelat-ch5-8/gates/14-not-cca2/pack.md =====

# Gate 14 · the PRF scheme is not CCA2-secure (`prfFixedScheme_not_cca2`)

Round 1. Auditor Codex (Seyoon's choice, 2026-11-11). Draft
[PR #289](https://github.com/Shilun-Allan-Li/tcslib/pull/289) at
`7960d6d4c3254797fdec191fff72c8d4c0147e1a` on branch `land/pass-shelat-not-cca2`, targeting
`cryptography/pass-shelat-ch2-4` on base `fe757f17aa6bda2f711e69abe7e2470ce5872e04`. That base has the
post-#286 Lean content `ed0f7238`; later base commits are records only.

This proof audit covers the formerly admitted `Composability.prfFixedScheme_not_cca2`
(`Encryption/PrivateKey/OracleFromPRF.lean`) and the corollary `not_prfFixedScheme_cca2`, which now has
no admission. It also covers the authorized reader additions:
- `prfScheme_dec` in `PrivateKey/FromPRF.lean`;
- six specification-typed readers in `PrivateKey/OracleSecurity.lean`.

The source is [PS10], R. Pass and a. shelat, *A Course in Cryptography*, third edition, January 2010:
§7.1.3, p. 169 (Claim 169.a) and Algorithm 99.1. The fill ran in two rounds:
- **Round 1 (Codex):** delivered the adversary and the encryption frontier, then escalated a missing
  reader (`worker-report-r1.md`).
- **Round 2 (Claude):** added the readers authorized by the round-2 brief and completed the proof
  (`worker-report-r2.md`).

The bundle includes both briefs.

## The proof

1. **The adversary.** `cca2Next` and `cca2Adversary`: a uniform machine built with
   `ofPolyTimeUniform … (.const 0)`. Check the three activations:
   - on the empty log it asks the challenge on `⟨0ⁿ, 1ⁿ⟩`;
   - on one entry it asks `Dec` on the challenge with its last bit flipped;
   - on two entries it outputs the complement of the last message bit of the `Dec` answer.

   Check also the polynomial-time proof `cca2Next_poly`, built from closure combinators.
2. **The run.** `cca2Run` is stated for any `FixedLengthScheme` with a decryption hypothesis.
   - With budget `.const 2`, check that the third activation's output is read and the timeout is
     never reached.
   - Check that `Enc` is never queried.
   - Check that CCA2 answers the altered query because `c' ≠ c` (`cca2Alter_ne`; the width
     `3n + 2` is positive).
3. **The encryption frontier.** For `n > 0` the challenge is `⟨r, bⁿ ⊕ f_k(r)⟩`, padded to its
   exact width. Its last bit lies in the second component. Decryption of the altered ciphertext is
   `⟨1, bⁿ ⊕ e_{n−1}⟩` (`cca2Cipher`, `cca2Decrypt`, `cca2FlipBits_unmask`, `cca2LastBit`). Check
   that `n > 0` is used only for the last-bit position.
4. **The advantage.** For every key and coins the run returns `b`, so `IND_b` accepts with
   probability `if b then 1 else 0` and the advantage is `|0 − 1| = 1`.

## Interfaces and discipline

- **Statement freeze.** The target header and every older declaration are unchanged; 7 public
  declarations are added.
- **The readers.**
  - Each must state its equation exactly, be public, not `@[simp]`, and have a docstring with its
    formula. `indImpl_dec_onSpec` casts the valid answer along `indSpec_decRng`; the review judged
    that the right form for sealed consumers. Do you agree?
  - The worker omitted `indImpl_enc_onSpec` and `indImpl_challenge_repeat_onSpec` as unused, per the
    brief. `_repeat_onSpec` is deferred to the `_cpa`/`_cca1` fills.
- **Rule 10.** No touched declaration may read another file's definition. Only `OracleFromPRF.lean`'s
  own `prfFixedScheme` may be unfolded; it is not.
  - Casts are removed only through `cast_cast` and `cast_eq` on explicit double casts.
  - `cca2OfFn_cast` uses the width equalities from published readers.
- **Landing-edit commit.** It changes no statement and no route:
  - the docstrings now say the claim is proved;
  - the unused helper `cca2Unmask` is deleted;
  - the private copy of `GGMRed.ofFn_padFin_of_length` is replaced by that lemma (DL-31).

## Evidence

- `review.md`: the maintainer's independent review.
- `verification.zip`: its raw evidence:
  - integrity, and a fresh build of the 238-module closure on the landing branch before the edits;
  - the admission census, statement comparison and axiom census;
  - whole-file closure seals of the three files with base seals;
  - controls and the explicit-reader scan.
- `landing/` (on the PR head):
  - `closure-build.jsonl`: the review's 238-module build, before the landing edits;
  - `edit-rebuild.jsonl`: the 4 modules affected by the edits, rebuilt;
  - `root-checks.jsonl`: 18 downstream modules through `TCSlib` and `Checks` on the full tree;
  - `axioms.log`: the target, the corollary and two readers print
    `[propext, Classical.choice, Quot.sound]`. The probe's `prfScheme_dec` line used a wrong
    namespace; the review's axiom census covers it.
- `sources.zip`: the source closure at the head (129 modules plus the facade).

## Findings delivery

Return `gate14-not-cca2-findings.md` as a Markdown file in this chat. For multiple evidence files,
return a ZIP. The user dispatches and merges.

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

## ===== briefs/pass-shelat-ch5-8/gates/14-not-cca2/review.md =====

# not-cca2 · maintainer delivery review (round 2 final)

**Verdict: ACCEPT WITH LANDING EDITS** (0 blockers, 0 majors, 4 minors, 3 notes).

Delivery: round 1 Codex (checkpoints 1–2, escalation), round 2 Claude, exchange `b7604844`
(`inbox/fills/not-cca2/`); 3 patches on `4a09f3993eb9344fc5714610e41ab141a0144db8`. Independent
review on a landing branch on the post-#286 head; evidence `review-evidence.zip` (SHA-256 `27ba267b220c4b3cf842606b4e9d1fcf73ab4423b30fdddcfda4287365104439`;
inner `SHA256SUMS` 364 files, pins in `PROVENANCE.txt`).

## Checks (re-run by the reviewer)
- Integrity: payload sums 429/429; `git am` reproduces `src/` byte for byte.
- Landing build (fresh tree, `fillinputs.py` order of 238 modules): 238/238 rc 0, 0 errors.
- Admissions: landing parent 32 → head 31; only `prfFixedScheme_not_cca2` removed.
- Statements: 0 changed, 0 removed; 7 public added (`prfScheme_dec`, 6 readers).
- Axioms: target, corollary, `prfScheme_dec` and readers standard; over all 218 stored constants
  of the three modules only `_cpa`/`_cca1` carry `sorryAx`.
- Rule 10: whole-file closure seals (1754 / 678 / 1842 requests) 0 errors; base seals 0 errors;
  6 control probes ALL_OK; explicit-reader scan 318 items, 0 foreign.
- Lint 0 FAIL (same 5 WARN as base).

## Findings and dispositions
| # | Severity | Finding | Disposition |
|---|---|---|---|
| 1 | minor | Stale module docstring in `OracleFromPRF.lean` ("stated; a `sorry`"). | **Landing edit.** |
| 2 | minor | Stale facade docstring `PrivateKey.lean` ("also pending"). | **Landing edit.** |
| 3 | minor | Dead round-1 helper `cca2Unmask`. | **Landing edit:** deleted. |
| 4 | minor | `cca2OfFn_padFin` duplicates `GGMRed.ofFn_padFin_of_length`. | **Landing edit:** replaced; DL-31 tracks the shared home. |
| 5 | note | Reader set omits `indImpl_challenge_repeat_onSpec`/`_enc_onSpec` (unused). | Consistent with the brief; `_repeat_onSpec` deferred to the `_cpa`/`_cca1` fills. |
| 6 | note | `indImpl_dec_onSpec` casts the answer (unlike the public-key file). | Correct form for sealed consumers; kept. |
| 7 | note | Patch 3 titled "r2 checkpoint 1" holds the final content. | Recorded; history kept as delivered. |

## Landing
Branch `land/pass-shelat-not-cca2` at `7960d6d4c3254797fdec191fff72c8d4c0147e1a` (3 delivered commits +
landing edits) on the post-#286 head. After the edits: the 4 affected modules rebuilt (0 errors),
downstream through `TCSlib` and `audits/pass-shelat/Checks` (18 modules) rc 0 on the full tree,
axioms standard (`landing/`). PR #289 (draft).

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

## ===== briefs/pass-shelat-ch5-8/fills/not-cca2/issued-r1/brief.md =====

# Codex fill · the §3.9 scheme is not CCA2-secure (`prfFixedScheme_not_cca2`)

**Issue base** `4a09f3993eb9344fc5714610e41ab141a0144db8` on `cryptography/pass-shelat-ch2-4`
(later campaign commits are records only).
**Unit** `not-cca2`. **Worker** Codex. **Lean** 4.25.0 and the Mathlib revision in that commit's
`lake-manifest.json`.

Prove the admitted theorem `Composability.prfFixedScheme_not_cca2` in
`TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF.lean` [PS10, §7.1.3, p. 169,
Claim 169.a]: an explicit adversary with a constant query budget has advantage exactly `1`
against the scheme of Algorithm 99.1 in the CCA2 game, at every `n > 0` and for every family
`F`. The proved corollary `not_prfFixedScheme_cca2` then holds without admissions. The
statement passed Gate 04.

## Checkout and delivery (Codex)

- Fetch `cryptography/pass-shelat-ch2-4` and start a local branch `fill/not-cca2` at the exact
  issue base above. Record the base in `REPORT.md`. Do not push any branch.
- Read `policy.md`, the attached environment addendum and `README.md`.
- **Return each checkpoint and the final delivery in the chat**, clearly labelled, as a ZIP with
  `not-cca2/` at its root containing `REPORT.md`, `patches/` (the whole `git format-patch` series
  from the issue base), `src/` (the final owned files under their repository paths) and
  `evidence/`. A self-contained Markdown delivery with the same content is also acceptable.
  Do not push to GitHub. The maintainer files your delivery under `inbox/fills/not-cca2/` and
  reviews it for a PR that Seyoon approves.

## Target

The source declaration is frozen. This quote comes directly from the issue base (line 143).
The section variables are `F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)`,
`E : List Bool → List Bool`, `hE : PolyTimeComputable E` and
`hFE : ∀ n s x, E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x)`.

```lean
theorem prfFixedScheme_not_cca2 :
    ∃ (A : NUPPT) (q : PolyExpr), ∀ n, 0 < n →
      advantage ((prfFixedScheme F E hE hFE).indGame .cca2 A (q.eval n) false n)
        ((prfFixedScheme F E hE hFE).indGame .cca2 A (q.eval n) true n) = 1 := by
  sorry
```

The game (`FixedLengthScheme.indGame`, `Encryption/PrivateKey/OracleSecurity.lean`) samples the
key-generation coins and `A`'s coins and simulates `A.toComp (S.indCodec n) n q r` against three
oracles (`indImpl`): `Enc` (index 0, `n`-bit messages), `Dec` (index 1, `(3n+2)`-bit ciphertexts,
answers `⟨1, m⟩` or `⊥`; under CCA2 it refuses only the recorded challenge) and `Challenge`
(index 2, `2n`-bit query `⟨m₀, m₁⟩`, answers `Enc_k(m_b)` once and repeats it). The output is
`A`'s one-bit result.

## Published interfaces

Read every definition of another file through these published lemmas (policy §1, rule 10).
`OracleFromPRF.lean`'s own `prfFixedScheme` may be unfolded, but prefer its readers.

| Interface | Provider |
|---|---|
| `prfFixedScheme_toPrivateKeyScheme`, `prfFixedScheme_ctLen` (simps), `prfFixedScheme_gen/_enc/_dec` | `Encryption/PrivateKey/OracleFromPRF.lean` (owned) |
| `prfScheme_gen`, `prfScheme_enc`, **`prfScheme_dec` (to add, see Scope)**, `runAt_prfEnc`, `runAt_prfDec`, `decodeFin_runAt_prfDec_of_not_wf`, `polyTimeComputable_prfEncFun/_prfDecFun` | `Encryption/PrivateKey/FromPRF.lean` |
| `runAt_coinKey` | `Encryption/PrivateKey/FromPRG.lean` |
| `inLens_zero/_one/_two`, `outLens_zero/_one/_two`, `indSpec_eq`, `decOpen_cca2`, `encryptAt_eq`, `decAnswer_some/_none`, `splitHalf_fst/_snd`, `indImpl_enc/_dec/_challenge_none/_challenge_repeat/_dec_cca2_challenge`, `indCodec_decodeMove/_encodeEntry/_timeout`, `indGame_eq` | `Encryption/PrivateKey/OracleSecurity.lean` |
| `NUPPT.ofPolyTimeUniform`, `coins_ofPolyTimeUniform`, `ofPolyTimeUniform_uniform`, `runAtL_ofPolyTimeUniform`, `runAt_eq`, `coinLen_eq`, `coinsEquiv_ofPolyTimeUniform(_ofFn)`, `inArg_eq`, `inParam_eq`, `inCoins_eq`, `advInput_eq` | `Complexity/Randomized/PPT.lean`, `NonUniform.lean`, `Closure.lean` |
| `NUPPT.toComp_eq`, `buildComp_zero_of_ret/_of_query`, `buildComp_succ_of_ret/_of_query` | `Games/Machines.lean` |
| `bitCodec_decodeMove`, `bitCodec_encodeEntry`, `bitCodec_timeout`, `decodeBitMove_query`, `decodeBitMove_ret`, `encodeLog_bitCodec`, `zeroBits_apply`, `ofFn_zeroBits` | `Games/BitCodec.lean` |
| `simulate` equations and `OracleComp` pure/bind/query laws | `Games/Simulate.lean`, `Games/OracleComp.lean` |
| `accept_eq`, `advantage_eq`, `prob_bind`, `prob_pure`, `expect_*`, `sample_eq` | `Games/Advantage.lean`, `Games/Probability.lean` |
| `pairEncode_eq_dbl`, `pairDecode_pairEncode`, `pairFstD_pairEncode`, `pairSndD_pairEncode`, `length_pairEncode`, `decodeFin_ofFn`, `padFin` readers | `Complexity/TuringMachine/Encoding.lean`, `Asymptotic/Adversary.lean` |

`NUPPT.Coins`, `bitSpecAt`, `bitSpec`, `QueryImpl` and `indSpec` are abbreviations;
`PolyExpr.eval` is notation. If another needed equation has no published reader, record it in
`REPORT.md` and use the escalation route; do not unfold the foreign definition.

## Proof route and checkpoints

The docstring sketch is the route.

1. **The adversary.** Define a polynomial-time string function on `A`'s activation input (its
   encoded log, read through `toComp_eq`, `encodeLog_bitCodec` and the decoder cases) that:
   with an empty log, moves `Challenge ⟨0^n, 1^n⟩`; with one entry (the challenge answer `c`),
   moves `Dec c'` where `c'` is `c` with its last bit flipped; with two entries, outputs
   `¬ m'_{n-1}` where the second entry's answer is `⟨v, m'⟩`. Build `A` with
   `NUPPT.ofPolyTimeUniform` and choose a constant budget `q` (for example `.const 2`; check
   how `buildComp` spends its budget so that the third activation's output is read). Prove the
   function polynomial-time from the closure combinators. Send checkpoint 1.
2. **The challenge.** For `n > 0`, the challenge in `IND_b` is
   `padFin (3n+2) (pairEncode r (b^n ⊕ f_k(r)))` (`encryptAt_eq`, `prfFixedScheme_enc`,
   `prfScheme_enc`, `runAt_prfEnc`, `hFE`, `runAt_coinKey`). Its length is exactly `3n + 2`, and
   its last bit lies in the second component (`pairEncode_eq_dbl`). Flipping it gives `c' ≠ c`,
   still well-formed, with second component `b^n ⊕ e_{n-1} ⊕ f_k(r)`. Send checkpoint 2.
3. **The decryption answer.** Under CCA2 with state `some c` and query `c' ≠ c`, `Dec` answers
   `decAnswer (decodeFin n (Dec_k ⟨r, …⟩))` (`indImpl_dec`, `decOpen_cca2`). With
   `prfFixedScheme_dec`, the new `prfScheme_dec` and `runAt_prfDec`, the answer is
   `⟨1, b^n ⊕ e_{n-1}⟩`, so its last message bit is `¬ b`. Send checkpoint 3.
4. **The advantage.** For every key and coins, the simulation returns `b` (step 1 reads the
   answers off the log). So `indGame .cca2 A q b n` returns `b` with probability `1`, its
   acceptance is `0` for `b = false` and `1` for `b = true`, and the advantage is `|0 − 1| = 1`.
   Send the final delivery.

Check: `n > 0` is used only for the last-bit position; the `Enc` oracle is never queried; the
timeout output is not reached with the chosen budget.

## Scope and proof discipline

- Own `TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF.lean`: replace the one proof body
  and add helpers there (keep the file below 1000 lines).
- **Authorized reader addition.** In `TCSlib/Cryptography/Encryption/PrivateKey/FromPRF.lean`,
  add exactly one public theorem beside `prfScheme_gen`/`prfScheme_enc`, in the same form:
  `prfScheme_dec : (prfScheme F E hE hFE).dec = NUPPT.ofPolyTimeUniform
  (polyTimeComputable_prfDecFun hE) (.const 0) := rfl`, with a docstring stating that formula.
  Change nothing else in that file.
- You may edit the target's proof sketch to describe the delivered proof. Preserve the statement,
  every other declaration (including the admitted `prfFixedScheme_cpa`/`_cca1`), the statement
  prose and the global simp attributes. Public helpers get a docstring with their formula and a
  proof sketch when nontrivial (policy §3). Do not edit any other file.
- Use published readers for other files' definitions in tactics and in term elaboration,
  including generated matchers and projections. For core and Mathlib use their equation lemmas
  in `simp`, `rw` and `unfold`.
- **Escalation.** If the target appears false, or a required reader is missing with no clean
  route, write the exact failing obligation and the smallest proposed correction in `REPORT.md`
  and return a checkpoint. At a partial delivery identify the remaining admission and the
  checked frontier.

## Checks and report

- Bootstrap from `order.txt` and the narrow `roots.txt` using the environment addendum. Check one
  module per `scripts/lean_check_tree.sh` invocation; one Lean process per olean tree; never
  `lake build`, never an unfiltered cache get; Python as `python3 -I`.
- Recheck `PrivateKey/FromPRF` and `PrivateKey/OracleFromPRF`, then sweep the rest of the supplied
  order (it includes every module downstream of `FromPRF`). Compare `sorry` warnings with
  `base-sorries.txt`: the only change must be the removed `prfFixedScheme_not_cca2`.
- Print the axioms of `prfFixedScheme_not_cca2` and `not_prfFixedScheme_cca2` (only `propext`,
  `Classical.choice`, `Quot.sound`).
- Collect foreign references from the elaborated new proofs, including generated matcher and
  projection helpers. Run an instance-aware seal of the touched declarations with the full
  candidate list, plus a control that passes before sealing and fails after sealing. Report the
  candidates, controls and any findings. Include the explicit-unfold scan and
  `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Encryption/PrivateKey --check8b`.
- Report the issue base, the target's status, exact changed files and sketch edits, new helper
  declarations, any reader requests, and the resource, cache, bootstrap, sweep, axioms, seals and
  lint evidence.

**Ready to dispatch**

## ===== briefs/pass-shelat-ch5-8/fills/not-cca2/issued-r2/brief.md =====

# Claude fill · not-cca2 continuation (`prfFixedScheme_not_cca2`, round 2)

**Issue base** `4a09f3993eb9344fc5714610e41ab141a0144db8` on `cryptography/pass-shelat-ch2-4`.
**Unit** `not-cca2`. **Worker** Claude (continuation of a Codex partial delivery). **Lean** 4.25.0
and the Mathlib revision in that commit's `lake-manifest.json`.

The round-1 brief (`brief-r1.md` in this pack) still governs the target, route, checks and
discipline; this brief states only what changes. Round 1 (Codex) delivered checkpoint 2 as an
**escalation**: the target is still admitted, and the challenge-oracle reader at the
specification's widths is missing. Its payload is on the exchange at `inbox/fills/not-cca2/`
(worker head `9f057f65bbb1b1795dd30a179c47b5b670a01452`, not published; two patches).

## Start from the round-1 work

- Fetch `cryptography/pass-shelat-ch2-4` and start a local branch `fill/not-cca2` at the issue base.
  Apply `inbox/fills/not-cca2/patches/0001-*.patch` and `0002-*.patch` with `git am`. Check that the
  result equals `inbox/fills/not-cca2/src/` byte for byte. Record this in `REPORT.md`.
- Read `inbox/fills/not-cca2/REPORT.md` and `evidence/READER-REQUEST.md`. Reuse what is checked
  (the adversary `cca2Next`/`cca2Adversary`, the encryption frontier, `prfScheme_dec`); you may
  restructure or replace any of the private helpers. Treat that payload as working material.

## Resolution of the escalation: authorized readers

The private-key oracle file lacks the readers at the specification's types that the public-key
file already has (`Encryption/PublicKey/OracleSecurity.lean`: `indSpec_dom`, `indSpec_rng`,
`indSpec_decDom`, `indSpec_challengeDom`, `indSpec_challengeRng`, `indImpl_dec_onSpec`,
`indImpl_challenge_none_onSpec`, `indImpl_challenge_repeat_onSpec`). You may add their
private-key counterparts to **`TCSlib/Cryptography/Encryption/PrivateKey/OracleSecurity.lean`**,
beside the existing `indImpl_*` readers, in the same form:

- width readers for the three oracles of `FixedLengthScheme.indSpec n` (index 0 `Enc`, 1 `Dec`,
  2 `Challenge`): `(S.indSpec n).dom i = …` and `(S.indSpec n).rng i = …`, proved through
  `indSpec_eq`, `bitSpec`'s published readers and `inLens_*`/`outLens_*`;
- `indImpl_enc_onSpec`, `indImpl_dec_onSpec`, `indImpl_challenge_none_onSpec`,
  `indImpl_challenge_repeat_onSpec`: the existing equations restated for an argument of the
  specification's type, with the width conversions as explicit `cast`s along those readers, proved
  `by simpa only [cast_eq] using S.indImpl_… …` (or `rfl`).

Add only the readers you use (the challenge pair is required; add the `Dec` ones if the CCA2 step
needs them). Each is public, not `@[simp]`, with a docstring stating its formula. Change nothing
else in that file. The round-1 reader proposal `indImpl_challenge_none_cast` is an acceptable
alternative form if the `_onSpec` form does not elaborate under seal; say which you used and why.

## Scope (replaces the round-1 scope's file list)

- Owned: `PrivateKey/OracleFromPRF.lean` (the target body and private helpers, below 1000 lines).
- Authorized additions: `PrivateKey/FromPRF.lean`, exactly `prfScheme_dec` (as in round 1);
  `PrivateKey/OracleSecurity.lean`, exactly the readers above.
- Everything else in round 1's scope and discipline holds: the target statement and every other
  declaration are frozen; published readers only for other files' definitions (the new
  `OracleSecurity` readers are now published readers for `OracleFromPRF`); escalate with the exact
  failing obligation if blocked.

## Delivery (Claude)

Deliver every checkpoint and the final payload under `inbox/fills/not-cca2/` on
`exchange/pass-shelat-ch5-8`, **replacing** the round-1 payload files there (the maintainer has
archived the originals under `archive/fills/not-cca2/`). Include `REPORT.md`, `patches/` (the whole
`git format-patch` series from the issue base, round-1 patches included), `src/` (all changed files)
and `evidence/`. Commit messages `fill not-cca2: r2 checkpoint N` and `fill not-cca2: r2 final`.
Pull with rebase before pushing; push only that path; never force-push. Keep the proof branch
local. The maintainer reviews the delivery for a PR that Seyoon approves.

## Checks

As round 1, with the sweep over the full supplied `order.txt` (232 modules; it already contains
everything downstream of `PrivateKey/OracleSecurity`). Expected admissions: `base-sorries.txt`
minus `prfFixedScheme_not_cca2` (32). Axioms of `prfFixedScheme_not_cca2` and
`not_prfFixedScheme_cca2`: only `propext`, `Classical.choice`, `Quot.sound`. Seal the touched
declarations of all three changed files with controls, run the explicit-unfold scan, and run
`python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Encryption/PrivateKey --check8b`.

**Ready to dispatch**

## ===== briefs/pass-shelat-ch5-8/gates/14-not-cca2/worker-report-r1.md =====

# not-cca2 — escalation at checkpoint 2 (final partial delivery)

**The target remains admitted. This is not a completed fill.** Checkpoint 1 was
returned separately as `not-cca2-checkpoint1.zip`. Work stops at the issued brief's
missing-reader escalation route. The mathematical target has not been refuted.

## Escalation and requested correction

The published `FixedLengthScheme.indImpl_challenge_none` equation relies on implicit
identifications of its query and answer widths. A minimal client passes before
sealing `inLens` and `outLens`, but fails when those two foreign definitions are
irreducible, even when the client merely applies `heq_of_eq` to the published
reader. Direct application, an explicit query cast, and a heterogeneous-equality
consumer were tried; the width conversion remained blocked under the required seal.

The exact failing client, diagnostic, attempted consumer and smallest proposed
provider correction are in **`evidence/READER-REQUEST.md`**. This records failure of
the tested clean reader-only routes, not a proof that all possible transport
arguments are impossible.

The proposed `indImpl_challenge_none_cast` reader spells both input and output
casts explicitly. Its provider-side prototype and a client under sealed `inLens`,
`outLens` and `indImpl` compile with only the three permitted axioms. See
`evidence/ReaderProposal.lean` and `evidence/logs/reader-proposal.log`.
The proposal is review evidence only: it is absent from the production patches and
owned source. The issued scope authorizes no addition to OracleSecurity.lean, so
that file was not edited. A maintainer can publish the additional reader and issue
a continuation base.

## Exact source status and checked frontier

- Issue base: `4a09f3993eb9344fc5714610e41ab141a0144db8`.
- Exchange pin: `20ca57c15da54342358b27ae2fee359acf06560d`.
- Repository: `Shilun-Allan-Li/tcslib`; fresh separate checkout; local branch
  `fill/not-cca2`. No branch was pushed. The delivery head is in `evidence/delivery.json`.
- Lean 4.25.0; Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
- Only two tracked files changed, both under
  `TCSlib/Cryptography/Encryption/PrivateKey/`: `FromPRF.lean` adds exactly the
  authorized public `prfScheme_dec` reader, with its formula and proof `rfl`;
  `OracleFromPRF.lean` adds 28 private helpers and is 460 lines long.
- All original declarations, statements, statement prose, proof sketches and global
  simp attributes are preserved. There are no sketch edits and no new source admissions.
- The target `prfFixedScheme_not_cca2` still has its original `sorry`. The existing
  CPA/CCA1 admissions remain. The target and its corollary therefore still include
  `sorryAx`; the final axiom requirement has **not** been met.

The checked adversary is `NUPPT.ofPolyTimeUniform cca2Next_poly (.const 0)`. Its raw
activation equations ask Challenge on `0^n ++ 1^n`, then Dec on the last-bit-flipped
challenge answer, then output the negation of the last bit of the second answer.
Its polynomial-time proof uses the existing closure combinators. The intended
query budget is `.const 2`; its complete codec/`toComp` and simulation proof remains
pending. No new machine host was built.

The encryption frontier is checked for every key/coin string:

1. The selected half of the challenge query is the constant message `b`.
2. Every generated key and encryption nonce is an `n`-bit word.
3. The actual encryption word is `pairEncode (List.ofFn x) (List.ofFn (m + F n k x))`;
   its width is exactly `3*n+2`.
4. For `n>0`, modifying its last bit preserves the nonce and pairing prefix, keeps
   the width, and gives a distinct ciphertext with the last masked bit flipped.
5. At the list/vector algebra level, XOR-unmasking that payload gives the message
   with its last bit flipped.

The actual challenge-oracle assembly, CCA2 decryption-oracle proof, and final
probability/advantage calculation are not delivered. The failed challenge consumer
was removed from production source and retained verbatim in `evidence/attempts/`.

## Verification and limits

All seven issued pack entries match both their SHA-256 values and committed Git
bytes at the exchange pin. All 232 issued source hashes passed before editing.

The 129-module prerequisite closure was checked serially in supplied order. The
first target-file attempt exposed local proof errors, then the repaired target
passed. Both owned modules were rechecked at the final partial source; see
`logs/from-prf-final.log` and `logs/oracle-from-prf-final.log`. Every Lean check,
including probes, ran through `scripts/lean_check_tree.sh`, one module and one
Lean process at a time. The remaining 103 supplied downstream modules were not
swept after this escalation. The checked frontier is therefore the prerequisite
closure and the explicit probes, not the full 232-module acceptance sweep.

`logs/source-admissions.log` compares source admissions across all 232 supplied
modules: **33 at base, 33 now**, unchanged module by module. This is a source
comparison, not a replacement for the pending full warning sweep. The final
`#print axioms` output is in `logs/axioms-final-partial.log`; the elaborated helper
axiom census is in `logs/refs-final-partial.log`. New proved helpers use only
`propext`, `Classical.choice`, and `Quot.sound` (subsets allowed).

The type-and-value reference census includes generated helper declarations and
foreign definitions; the oracle input/output length definitions are explicitly
included as interface dependencies. `seal-candidates.json` lists every candidate,
its home module, instance/projection status and any exclusion. Reducible notation,
abbreviations and primitive structure projections are recorded separately; no
unsafe reducibility override is used. The seal harness also handles registered
instances by forwarding through an alias while sealing the original definition;
this frontier has no active foreign instance candidate. The retained production
frontier passes the final seal; its control passes before sealing and fails after
sealing at the intended `inArg` definitional equality. The unretained challenge
consumer's seal failure is the reported escalation, not hidden by that passing
frontier seal.

`logs/explicit-unfold-scan.log` finds only the owned `cca2Adversary` as an explicit
unfold target and no foreign explicit unfold/delta target. The required command
`python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Encryption/PrivateKey --check8b`
returns **0 FAIL, 5 WARN over 10 files**. The warnings name existing public definitions;
none of the new definitions is public. `git diff --check` passes.

## Environment and cache

Initial preflight: `nproc=9`; overlay disk free **59,564,011,520 bytes**; memory
headroom **9,525,805,056 bytes**, using `/proc/meminfo`'s `MemAvailable` fallback
because `/sys` and cgroup counters are not exposed. Both issued floors pass.
The clone, toolchain, cache, temporary files and oleans use the disk-backed overlay;
`/tmp` is tmpfs and was not used as `TMPDIR`.

The official Lean archive was freshly downloaded and extracted for this task;
its URL and SHA-256 are in `logs/toolchain-provenance.log`. No other session's
scratch dependency tree, package build, toolchain or olean store was reused.
The task-local cache store initially did not exist (0 files, 0 bytes). Only the
98 supplied direct Mathlib roots were requested. The initial cache fetch had 603
HTTP 429 failures; the allowed retry fetched those 603 and successfully unpacked
all **2,381 files**. No cleaned retry was needed. All present package URLs/revisions
match the manifest; the four unneeded documentation packages are ABSENT. Last pin
check: **PASS (all present packages match; order imports no absent package)**.
There are no zero-size package oleans, and the Mathlib-root import probe passed.

`/usr/bin/time` is absent. `time_check.py` records each module's UTC start/end,
elapsed/user/system times, exit status and maximum child RSS using Python's
`resource.getrusage`. All Python invocations used `python3 -I`. No project
`lake build` or unfiltered cache fetch was run; the cache tool's prescribed
internal bootstrap was left to Lake.

## New declarations and payload

The one new public declaration is **`prfScheme_dec`**. All following helpers are
private in the owned target file:

- List/vector operations: `cca2FlipLast`, `cca2FlipLast_poly`, `cca2FlipLast_snoc`,
  `cca2FlipLast_append`, `cca2FlipLast_pair`, `cca2FlipLast_length`, `cca2FlipLast_ne`,
  `cca2FlipBits`, `cca2FlipLast_ofFn`, `cca2FlipBits_unmask`, `cca2Unmask`,
  `cca2OfFn_padFin`.
- Adversary: `cca2Next`, `cca2Next_poly`, `cca2Adversary`, `cca2Adversary_run`,
  `cca2Adversary_one`, `cca2Adversary_two`.
- Encryption/challenge preparation: `cca2Encrypt`, `cca2Messages`,
  `cca2Messages_ofFn`, `cca2Messages_choice`, `cca2Alter`, `cca2Alter_ofFn`,
  `cca2Alter_ne`, `cca2CtLen`, `cca2Gen`, `cca2Cipher`.

No copied private proof or private machine implementation was introduced. Existing
published XOR and machine-reader lemmas are used directly.

`patches/` is the complete local `git format-patch` series from the issue base;
`src/` is the exact committed owned source. `evidence/` includes the issued inputs,
hashes, cache/bootstrap logs, final checks, census/seal/controls, failed attempts,
minimal interface reproducer and checked reader proposal. `evidence/delivery.json`
records the delivery head, source hashes and patch replay at the exact base using
a separate Git index. Checkpoint 1 remains a separate immutable chat artifact.

## ===== briefs/pass-shelat-ch5-8/gates/14-not-cca2/worker-report-r2.md =====

# not-cca2 — round 2, final delivery (Claude)

**Status: `Composability.prfFixedScheme_not_cca2` is proved; `not_prfFixedScheme_cca2` now holds
without admissions.** Both print exactly `[propext, Classical.choice, Quot.sound]`. The
232-module sweep passes with 32 admissions: `base-sorries.txt` minus the target.

## Provenance

- Issue base `4a09f3993eb9344fc5714610e41ab141a0144db8` on `cryptography/pass-shelat-ch2-4`.
  Exchange pin `409d4b0dd7485e6173504b2a2a850f1cb9214d0e`. The local branch `fill/not-cca2`, head
  `1e61d862f90fbfb3c25f076a277c400ba066a020`, is in a separate worktree and was never pushed.
  Lean 4.25.0, Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
- Pack: `sha256sum -c SHA256SUMS` in `outbox/fills/not-cca2/r2` gives 8/8 OK. All 232 issue-base
  sources match `SOURCE-SHA256SUMS`.
- **Round-1 start.** I applied round-1 patches `0001` and `0002` with `git am` at the base. The
  resulting `FromPRF.lean` (`a79e5b37…`) and `OracleFromPRF.lean` (`45cded6f…`) equal the round-1
  `src/` byte for byte (`evidence/logs/round1-apply.log`). Their commits carry a new committer
  but keep the original author and message.
- `patches/` holds the whole series from the base: `0001`, `0002` (round 1) and `0003` (round 2).
  Applying it with `git am` at the base reproduces `src/` (`evidence/logs/patch-replay-final.log`).
  Checkpoint 1 of round 2 is exchange commit `10d11e5a0`. The Lean sources have not changed since.

## Changed files

| File | Change |
|---|---|
| `PrivateKey/FromPRF.lean` | Round 1's authorized `prfScheme_dec` only (unchanged in round 2). |
| `PrivateKey/OracleSecurity.lean` | The authorized readers below; no other change (+46 lines). |
| `PrivateKey/OracleFromPRF.lean` | Target body; four new private helpers; the target's sketch (597 lines). |

### Readers added to `OracleSecurity.lean` (public, not `@[simp]`, docstrings with formulas)

They sit in one block after `indImpl_challenge_repeat`, beside the existing `indImpl_*` readers:

- `indSpec_decDom n : (S.indSpec n).dom 1 = (Fin (S.ctLen.eval n) → Bool)`
- `indSpec_decRng n : (S.indSpec n).rng 1 = (Fin (n + 1) → Bool)`
- `indSpec_challengeDom n : (S.indSpec n).dom 2 = (Fin (n + n) → Bool)`
- `indSpec_challengeRng n : (S.indSpec n).rng 2 = (Fin (S.ctLen.eval n) → Bool)`

  Each is proved by `rw [S.indSpec_eq, bitSpec_dom/rng, S.inLens_*/outLens_*]`.
- `indImpl_dec_onSpec`: the `indImpl_dec` equation for `c : (S.indSpec n).dom 1`, with the query
  read as `cast (S.indSpec_decDom n) c` and the valid answer as
  `cast (S.indSpec_decRng n).symm (decAnswer …)`.
- `indImpl_challenge_none_onSpec`: the `indImpl_challenge_none` equation for
  `mm : (S.indSpec n).dom 2`, with halves `splitHalf (cast (S.indSpec_challengeDom n) mm)` and the
  answer `cast (S.indSpec_challengeRng n).symm c`.

  Both are proved `by simpa only [cast_eq] using S.indImpl_…`.

I used the `_onSpec` form, not the round-1 alternative `indImpl_challenge_none_cast`. It
elaborates, and consumers pass under the seal (below). Unlike the public-key file's
`indImpl_dec_onSpec`, the private-key version also casts the **answer**. Without that cast, a sealed
consumer would have to identify `Fin (n + 1)` with `Fin (S.outLens n 1)` by unfolding.

**Readers deliberately not added**, because the proof does not use them: `indImpl_enc_onSpec`
(`Enc` is never queried) and `indImpl_challenge_repeat_onSpec` (the challenge is asked once). I
read "the challenge pair is required" as the challenge width readers
(`indSpec_challengeDom`/`_challengeRng`) with `indImpl_challenge_none_onSpec`. If the maintainer
meant the `none`/`repeat` equation pair, `repeat_onSpec` is a two-line addition in the same form.
I left it out to follow "add only the readers you use". **Please confirm at review.**

### New private helpers in `OracleFromPRF.lean`

Round 1's 28 helpers are reused unchanged. The new ones:

- `cca2Decrypt`: decrypting `⟨x, v⟩` of `n`-bit words under `k` decodes to `some (v + F n k x)`,
  through `prfFixedScheme_dec`, `prfScheme_dec`, `runAt_prfDec`, `hFE`, `zipWith_xor_ofFn_add`
  and `decodeFin_ofFn`.
- `cca2OfFn_cast`: `List.ofFn (cast h f) = List.ofFn f` for `h` from a width equality `a = b`
  (proved by `subst`). Every width conversion goes through this lemma and the published
  `inLens_*`/`outLens_*` equations.
- `cca2LastBit`: for `n > 0`, `(List.ofFn (Fin.cons true (cca2FlipBits fun _ => b))).getLastD false
  = !b`.
- `cca2Run`, the main simulation. It is stated for **any** `FixedLengthScheme` with nonempty
  ciphertexts, given that each decryption of a flipped challenge `Enc_k(b^n)` yields a message
  `v` whose answer `⟨1, v⟩` ends in `!b`. Under that hypothesis, `cca2Adversary` with budget `2`
  outputs `b` with probability `1`. The proof follows the three activations:
  - `toComp_eq` and `buildComp_succ_of_query`, twice, then `buildComp_zero_of_ret`;
  - `simulate_query`/`simulate_pure`, with `indCodec_decodeMove`/`_encodeEntry`,
    `encodeLog_cons/_nil`, `decodeBitMove_query/_ret` and the round-1 `cca2Adversary_run/_one/_two`;
  - the two new `_onSpec` readers, `decOpen_cca2`, `cca2Alter_ne`, `decAnswer_some`;
  - and `prob_bind`/`expect_const`/`prob_pure`.
- **Target body.** It uses `A = cca2Adversary` and `q = .const 2`. For each `b`, `accept` equals
  `if b then 1 else 0`. That comes from `indGame_eq`, `prob_bind`, `cca2Gen`, `cca2Run`,
  `cca2Cipher`, `cca2Decrypt` and `cca2FlipBits_unmask`. The advantage is then `|0 − 1| = 1`.

**Sketch edits.** Two places in the target's docstring, to describe the delivered proof. Step 1
adds "its query budget is `2`, so the third activation's output is read". Step 3 now reads "for
every key and all coins, `A` outputs `b` (`cca2Run`): `IND_b` accepts with probability `1` if
`b = 1` and `0` if `b = 0`". The statement, statement prose, all other declarations (including the
admitted `prfFixedScheme_cpa`/`_cca1`) and the global simp attributes are unchanged.

**One stale sentence, left for the maintainer.** The module docstring's "Main results" still
describes `prfFixedScheme_not_cca2` as "(Claim 169.a, stated; a `sorry` under its sketch)". The
brief authorizes edits only to the target's sketch, so I left that sentence unchanged. It should
now read "proved".

## Checks

- **Bootstrap.** The 129-module closure of `OracleFromPRF` (`evidence/bootstrap-order.txt`,
  identical to round 1's) ran serially. Modules 1–128 passed, the new `OracleSecurity` readers
  included. Module 129 (`OracleFromPRF`) failed on my first draft; the logged error is
  `Unknown identifier prob`. The fixed file was then rechecked on its own (logs under
  `evidence/logs/`; `bootstrap.tsv` records the failing first run as it happened).
- **Sweep.** The full supplied `order.txt` (232 modules) ran on the final source, in order, one
  module per `scripts/lean_check_tree.sh` call, one Lean process at a time: **232/232 pass**
  (`evidence/logs/sweep.tsv`, per-module logs in `logs/sweep/`). It took 974 s in total; the
  maximum child RSS was 3,134,384 KiB. `FromPRF` (147) and `OracleFromPRF` (162) are rechecked
  within it.
- **Admissions** (`evidence/logs/sweep-admissions.log`): 33 at the base, **32 now**. Every module
  is the same except `OracleFromPRF`, where 3 became 2 (only `prfFixedScheme_not_cca2` removed).
  The changed files raise no other warnings, except one pre-existing unused-simp-argument linter
  note at `FromPRF.lean:128` (`polyTimeComputable_prfDecFun`, untouched).
- **Axioms** (`evidence/logs/axioms-final.log`): `prfFixedScheme_not_cca2`,
  `not_prfFixedScheme_cca2`, `prfScheme_dec` and all six new readers depend on
  `[propext, Classical.choice, Quot.sound]`.
- **Reference census** (`evidence/probes/Refs.lean`, `evidence/logs/refs-final.log`). It
  enumerates the elaborated types and values of the 61 touched declarations of the three files:
  the 7 readers, and every `cca2` declaration of `OracleFromPRF` with generated matchers and
  auxiliaries. It lists each foreign TCSlib constant with its home module and its
  instance/projection status. `evidence/seal-candidates.json` gives each candidate's
  disposition. Reducible abbreviations and primitive projections are recorded but not sealed. So
  is `PolyExpr.eval`, which the brief exempts as notation. No foreign instance occurs; the
  instance-aware alias path of the harness is present but unused.
- **Seal** (`evidence/tools/make_seal.py`, `evidence/probes/Seal*.lean`). Each changed file's body
  is compiled in a probe module with every semireducible foreign candidate made
  `local irreducible`. For `OracleSecurity` and `FromPRF` the seal is applied in a section
  around the touched block. For `OracleFromPRF` it covers the whole body. The three seals are:
  - `OracleFromPRF`: 43 definitions, among them `inLens`, `outLens`, `indImpl`, `indCodec`,
    `bitCodec`, `decodeBitMove`, `buildComp`, `simulate`, `encodeLog`, `prob`/`expect`/`sample`,
    `NUPPT.toComp/runAt/ofPolyTimeUniform`, `decodeFin`, `padFin`, `pairEncode`, `prfScheme`,
    `prfDecFun`, `prfDecWF`;
  - `OracleSecurity`: 7;
  - `FromPRF`: 3.

  **All three pass**, with only the two pre-existing admissions in `OracleFromPRF`
  (`logs/seal-*.log`, `logs/seal-summary.log`).
- **Controls.** Each control passes before sealing and fails after it at the intended `rfl`:
  - `S.inLens n 2 = n + n` (`OracleFromPRF`; this is the round-1 escalation's identification);
  - `zeroBits d j = false` (`OracleSecurity`);
  - `pairEncode x a = …` (`FromPRF`).
- **Development note.** While developing, I prepended a temporary seal of the same kind to the
  owned file, then removed it before committing. That run found the problem with
  `simp only [cast_eq]`: unsealed, it strips the width casts by unfolding `outLens`. The final
  proof only removes a cast through `cast_cast` + `cast_eq` on explicit double casts (`hxc`,
  `hcc`), so it elaborates the same way with and without the seal.
- **Explicit-unfold scan** (`evidence/tools/unfold_scan.py`, `logs/explicit-unfold-scan.log`):
  PASS. The only `unfold` is of the owned `cca2Adversary`. No foreign definition name appears in
  any `rw`/`simp` list of the added lines.
- **Lint.** `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Encryption/PrivateKey
  --check8b` gives **0 FAIL, 5 WARN over 10 files**. The warnings are the same pre-existing
  public-def notes as round 1; none concerns a new declaration. `git diff --check` is clean, and
  no added line exceeds 100 characters.

## Environment, cache, resources

- **Preflight** (`logs/preflight.log`):
  - `nproc` 4;
  - no cgroup memory files, so the headroom is `MemAvailable` = 16,171,827,200 B (floor 4 GiB:
    PASS);
  - the clone, toolchain, payload and `/tmp` are on ext4 `/dev/vda`, with 22,684,639,232 B free
    when logged (floor 12 GiB: PASS). The figure was 27,685,502,976 B before the toolchain
    download; the logged preflight was written after it.

  No tmpfs was used.
- **Toolchain.** The official `lean-4.25.0-linux.tar.zst` was downloaded by this session, SHA-256
  `97bee7bda676ca54f4b1cebe323242a08323d75134fecd1ba31cee4db66abb8a` (equal to round 1's), and
  extracted with `TAR_OPTIONS=--no-same-owner`. `zstd` was installed from the package manager to
  extract it.
- **Cache.** The archive store `~/.cache/mathlib` did not exist beforehand (0 files, 0 bytes).
  The narrowed `lake exe cache get` covered the 98 roots, identical to `roots.txt`. It attempted
  2,381 downloads, decompressed 2,381 files and exited 0 with no failed download. No cleaned retry
  was needed.
- **Packages.** Every package present matches the manifest's URL and revision, and the order
  imports no absent package: **PASS (all present packages match)**. `doc-gen4`, `UnicodeBasic`,
  `BibtexQuery` and `MD4Lean` are ABSENT. No zero-size `.olean` (2,390 present). The
  Mathlib-root import probe passed.
- **Process discipline.** Every check, probe, bootstrap and sweep step ran through
  `scripts/lean_check_tree.sh`, one Lean process at a time, wrapped by `evidence/tools/time_check.py`
  for UTC start/end, elapsed time and maximum child RSS (`/usr/bin/time` is absent). No
  `lake build` and no unfiltered cache get. All Python ran as `python3 -I`. The peak was
  3,134,384 KiB RSS, with no OOM or resource symptom.

## Payload

- `REPORT.md`; `patches/0001-0003`; `src/` (the three changed files);
- `evidence/` with:
  - `inputs/`: the r2 pack, exchange README and `policy.md`;
  - `logs/`;
  - `probes/`: cache probe, axioms, census, seals, controls;
  - `tools/`;
  - `seal-candidates.json`, `bootstrap-order.txt`, `delivery.json`;
- `SHA256SUMS` over the payload.

## ===== TCSlib/Cryptography/Encryption/PrivateKey.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Encryption.PrivateKey.Scheme
import TCSlib.Cryptography.Encryption.PrivateKey.EnsembleSecurity
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRG
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.Hybrid
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine
import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag
-- Preserve the facade's existing permutation-to-PRG and hard-core exports.
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.FromPermutation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Private-key encryption

The ensemble games compare one ciphertext or a fixed vector of ciphertexts.
The oracle games give the adversary a query budget and specify its access to
encryption, the challenge and decryption.

## Main definitions

`TCSlib.Cryptography.PrivateKeyScheme` packages uniform polynomial-time algorithms
for key generation, encryption and decryption, with perfect correctness [PS10, Definition 24.7].
`TCSlib.Cryptography.PrivateKeyScheme.SingleMessageSecure` and
`TCSlib.Cryptography.PrivateKeyScheme.MultiMessageSecure` give the two ensemble games
[PS10, Definitions 91.1 and 93.1].
`TCSlib.Cryptography.Composability.FixedLengthScheme` adds a ciphertext length.
Its `indGame` defines the adaptive CPA, CCA1 and CCA2 games. `INDSecure` requires
negligible advantage in the selected game [PS10, Definition 168.1].

## Main results

`TCSlib.Cryptography.prgScheme_singleMessageSecure` proves single-message security
for the pad scheme given a secure PRG and a matching efficient evaluator
[PS10, Theorem 92.2].
`TCSlib.Cryptography.prfScheme_multiMessageSecure` proves security for fixed vectors
encrypted under one key with independent coins, given a PRF and a matching efficient
evaluator [PS10, Theorem 99.2].
`TCSlib.Cryptography.exists_multiMessageSecure_of_exists_prg` composes GGM with
the PRF scheme [PS10, Theorems 97.3 and 99.2].

## Contents

* `Encryption.PrivateKey.Scheme` gives the uniform polynomial-time scheme interface.
* `Encryption.PrivateKey.EnsembleSecurity` gives the ensemble games and their relations.
* `Encryption.PrivateKey.FromPRG` gives the PRG pad construction and its security proof.
* `Encryption.PrivateKey.FromPRF` gives the PRF scheme and its fixed-vector security proof
  [PS10, Algorithm 99.1 and Theorem 99.2].
* `Encryption.PrivateKey.FromPRF.Hybrid` proves the finite six-hybrid bound.
* `Encryption.PrivateKey.FromPRF.HybridLemmas` gives its probability and coin lemmas.
* `Encryption.PrivateKey.FromPRF.ReductionMachine` implements the next-query reduction.
* `Encryption.PrivateKey.OracleSecurity` gives the fixed-length interface and adaptive oracle games.
* `Encryption.PrivateKey.OracleFromPRF` gives the fixed-length PRF scheme and its oracle claims.
  The CPA and CCA1 proofs `prfFixedScheme_cpa` and `prfFixedScheme_cca1` are pending
  [PS10, Theorem 168.2]. The CCA2 counterexample `prfFixedScheme_not_cca2` is proved
  [PS10, §7.1.3, Claim 169.a], and so is `not_prfFixedScheme_cca2`.
* `Encryption.PrivateKey.EncryptThenTag` gives the encrypt-then-tag scheme, which tags the
  whole ciphertext under an independent key [PS10, Algorithm 169.3].
  The CCA2 proof `ccaScheme_cca2` is pending [PS10, Theorem 170.4].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, §2.1, §§3.6–3.9 and §7.1.3.
-/

## ===== TCSlib/Cryptography/Encryption/PrivateKey/FromPRF.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCoreLoops
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRG
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.Hybrid
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Multi-message secure encryption from a pseudorandom function

The key generator samples a key. The encryptor samples an independent point, masks the
message with the function value at that point, and returns the point with the masked message.
Decryption recomputes the mask and checks the ciphertext format [PS10, Algorithm 99.1].

## Main definitions

* `prfEncFun`, `prfDecFun` and `prfScheme` implement the scheme from a polynomial-time evaluator.
* `encodeTuple` encodes the fixed vector of ciphertext pairs as a string.

## Main results

* `prfScheme_multiEncDist` identifies the ciphertext sampler with the encoded real hybrid.
* `prfScheme_multiMessageSecure` lifts the six-hybrid bound to a negligible advantage against
  non-uniform polynomial-time distinguishers [PS10, Theorem 99.2].
* `exists_multiMessageSecure_of_prf` and `exists_multiMessageSecure_of_exists_prg` give the
  existence results from a PRF and, via GGM, from a PRG.

## Contents

* `FromPRF.Hybrid` proves the concrete six-hybrid bound.
* `FromPRF.HybridLemmas` supplies the collision and coin-relabelling estimates.
* `FromPRF.ReductionMachine` implements the next-query reduction and proves its run agreement.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.7, Definition 93.1, and §3.9, Algorithm 99.1 and Theorem 99.2.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4 (oracle adversaries and PRF advantage).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### The scheme of [PS10, Algorithm 99.1] -/

/-- The raw string function of `Enc` of [PS10, Algorithm 99.1]: on the machine layout
`⟨⟨⟨1^n, ⟨k, w⟩⟩, α⟩, r⟩` output the pair `⟨r, w ⊕ E(⟨k, r⟩)⟩`, where `E` evaluates the PRF on
`⟨key, input⟩` and the coin string `r` is the fresh point. -/
def prfEncFun (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  pairEncode (NUPPT.inCoins z)
    (List.zipWith xor (pairSndD (NUPPT.inArg z))
      (E (pairEncode (pairFstD (NUPPT.inArg z)) (NUPPT.inCoins z))))

/-- Whether the ciphertext `⟨r, c⟩` of the layout `⟨⟨⟨1^n, ⟨k, ⟨r, c⟩⟩⟩, α⟩, r'⟩` has `n`-bit
components: the domain of `Dec` in [PS10, Algorithm 99.1]. -/
def prfDecWF (z : List Bool) : Bool :=
  decide ((pairFstD (pairSndD (NUPPT.inArg z))).length = (NUPPT.inParam z).length) &&
    decide ((pairSndD (pairSndD (NUPPT.inArg z))).length = (NUPPT.inParam z).length)

/-- The raw string function of `Dec` of [PS10, Algorithm 99.1]: on the layout
`⟨⟨⟨1^n, ⟨k, ⟨r, c⟩⟩⟩, α⟩, r'⟩` with `n`-bit `r` and `c`, output `c ⊕ E(⟨k, r⟩)`; on any other
ciphertext, output `⊥`, here the `(n + 1)`-bit string `1^{n+1}`, which decodes to no message.

The source defines `Dec` on pairs of `n`-bit strings only. The guard matters under
chosen-ciphertext attacks: `E` agrees with `F` only on `⟨s, x⟩` with `|s| = |x|`, so without it a
malformed ciphertext would evaluate `E` where it is unconstrained, and there it may reveal the
key. -/
def prfDecFun (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  if prfDecWF z then
    List.zipWith xor (pairSndD (pairSndD (NUPPT.inArg z)))
      (E (pairEncode (pairFstD (NUPPT.inArg z)) (pairFstD (pairSndD (NUPPT.inArg z)))))
  else true :: NUPPT.inParam z

/-- `prfEncFun E` is polynomial-time when `E` is: projections, one evaluation of `E`, one
bitwise exclusive-or (`Complexity.polyTimeComputable_pairXor`) and one pairing. -/
theorem polyTimeComputable_prfEncFun {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (prfEncFun E) := by
  have h := NUPPT.polyTimeComputable_inCoins.pairEncode
    (polyTimeComputable_pairXor.comp
      ((polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg).pairEncode
        (hE.comp ((polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg).pairEncode
          NUPPT.polyTimeComputable_inCoins))))
  convert h using 1
  funext z
  simp [prfEncFun, Function.comp_apply]

/-- The well-formedness test of `Dec` is polynomial-time: two length comparisons
(`Complexity.polyTimeComputable_lenEq`). -/
theorem polyTimeComputable_prfDecWF : PolyTimeComputable (fun z => [prfDecWF z]) := by
  have hl : ∀ g : List Bool → List Bool, PolyTimeComputable g →
      PolyTimeComputable (fun z => [decide ((g z).length = (NUPPT.inParam z).length)]) := by
    intro g hg
    convert polyTimeComputable_lenEq.comp (hg.pairEncode NUPPT.polyTimeComputable_inParam)
      using 1
    funext z
    simp [Function.comp_apply]
  exact polyTimeComputable_and
    (hl _ ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).comp
      NUPPT.polyTimeComputable_inArg))
    (hl _ ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD).comp
      NUPPT.polyTimeComputable_inArg))

/-- `prfDecFun E` is polynomial-time when `E` is: the guard, then the branch of the old `Dec`
(`Complexity.polyTimeComputable_ite`). -/
theorem polyTimeComputable_prfDecFun {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (prfDecFun E) := by
  refine polyTimeComputable_ite polyTimeComputable_prfDecWF ?_
    ((polyTimeComputable_const [true]).append NUPPT.polyTimeComputable_inParam)
  have h := polyTimeComputable_pairXor.comp
    (((polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD).comp
        NUPPT.polyTimeComputable_inArg).pairEncode
      (hE.comp ((polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg).pairEncode
        ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).comp
          NUPPT.polyTimeComputable_inArg))))
  convert h using 1
  funext z
  simp [prfDecFun, Function.comp_apply]

/-- The activation of the encryption machine on `⟨k, w⟩` with coins `r` is
`⟨r, w ⊕ E(⟨k, r⟩)⟩`. -/
theorem runAt_prfEnc {E : List Bool → List Bool} (hE : PolyTimeComputable E) (coins : PolyExpr)
    (n : ℕ) (k w : List Bool)
    (r : (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) coins).Coins n) :
    (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) coins).runAt n (pairEncode k w) r =
      pairEncode (List.ofFn r) (List.zipWith xor w (E (pairEncode k (List.ofFn r)))) := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [prfEncFun, NUPPT.inArg_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq]

/-- The activation of the decryption machine on `⟨k, ⟨r, c⟩⟩` with `n`-bit `r` and `c` is
`c ⊕ E(⟨k, r⟩)`. -/
theorem runAt_prfDec {E : List Bool → List Bool} (hE : PolyTimeComputable E) (coins : PolyExpr)
    (n : ℕ) (k r c : List Bool) (hr : r.length = n) (hc : c.length = n)
    (r' : (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) coins).Coins n) :
    (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) coins).runAt n
        (pairEncode k (pairEncode r c)) r' =
      List.zipWith xor c (E (pairEncode k r)) := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [prfDecFun, prfDecWF, NUPPT.inArg_eq, NUPPT.inParam_eq, NUPPT.advInput_eq, hr, hc]

/-- On a ciphertext `w` whose two projections `pairFstD w` and `pairSndD w` are not both `n` bits
long, the decryption machine outputs `⊥`: a string that decodes to no `n`-bit message. -/
theorem decodeFin_runAt_prfDec_of_not_wf {E : List Bool → List Bool} (hE : PolyTimeComputable E)
    (coins : PolyExpr) (n : ℕ) (k w : List Bool)
    (hw : ¬ ((pairFstD w).length = n ∧ (pairSndD w).length = n))
    (r' : (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) coins).Coins n) :
    decodeFin n ((NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) coins).runAt n
        (pairEncode k w) r') = none := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  have hf : prfDecWF (pairEncode (pairEncode (NUPPT.advInput n (pairEncode k w)) [])
      (List.ofFn r')) = false := by
    simp only [prfDecWF, NUPPT.inArg_eq, NUPPT.inParam_eq, NUPPT.advInput_eq, pairFstD_pairEncode,
      pairSndD_pairEncode, List.length_replicate, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    tauto
  rw [prfDecFun, hf]
  simp [decodeFin_eq, NUPPT.inParam_eq, NUPPT.advInput_eq]

/-- Masking twice with the same pad (at least as long as the message) is the identity
(private copy of the helper of `Encryption/PrivateKey/FromPRG.lean`). -/
private theorem zipWith_xor_xor_self : ∀ (m p : List Bool), m.length ≤ p.length →
    List.zipWith xor (List.zipWith xor m p) p = m
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | a :: m, b :: p, h => by
    simp only [List.zipWith_cons_cons, List.cons.injEq]
    exact ⟨by cases a <;> cases b <;> rfl, zipWith_xor_xor_self m p (by simpa using h)⟩

/-- **The many-message encryption scheme of [PS10, Algorithm 99.1]** for a function family
`F` with polynomial-time evaluator `E` on `⟨s, x⟩`: `Gen(1^n)` outputs a uniform `n`-bit key
`k` (its coin string); `Enc_k(m)` draws `r ← U_n` (its coin string) and outputs
`⟨r, m ⊕ f_k(r)⟩`; `Dec_k(⟨r, c⟩) = c ⊕ f_k(r)` (deterministic, coins `const 0`). Correctness is
`(m ⊕ p) ⊕ p = m` with the `n`-bit pad `p = f_k(r)`.

**Deviation:** `prfScheme`: the key is the `n`-bit coin string of `Gen`; `Enc` draws its `n`-bit
`r` as its coin string; the evaluator `E` of the PRF is an explicit argument rather than
extracted from `PRF.easy`; ciphertexts are the pair `⟨r, m ⊕ f_k(r)⟩`. -/
noncomputable def prfScheme (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x)) :
    PrivateKeyScheme where
  gen := NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD .var
  enc := NUPPT.ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) .var
  dec := NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) (.const 0)
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  enc_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  dec_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  correct := by
    intro n m rg re rd
    rw [runAt_coinKey, runAt_prfEnc hE]
    have h : E (pairEncode (List.ofFn rg) (List.ofFn re)) =
        List.ofFn (F n (NUPPT.coinsEquiv_ofPolyTimeUniform _ _ n rg)
          (NUPPT.coinsEquiv_ofPolyTimeUniform _ _ n re)) := by
      rw [← hFE, NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn, NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn]
    have hre : (List.ofFn re).length = n := by
      rw [← NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn _ _ n re, List.length_ofFn, PolyExpr.eval_var]
    rw [h, runAt_prfDec hE _ _ _ _ _ hre (by simp), h,
      zipWith_xor_xor_self _ _ (by simp), decodeFin_ofFn]

/-- The key generator of `prfScheme` is the uniform machine returning its coin string
[PS10, Algorithm 99.1]. -/
theorem prfScheme_gen (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (F n s x)) :
    (prfScheme F E hE hFE).gen = NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD .var := rfl

/-- The encryptor of `prfScheme` uses its raw encryption function and `n` coins
[PS10, Algorithm 99.1]. -/
theorem prfScheme_enc (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (F n s x)) :
    (prfScheme F E hE hFE).enc =
      NUPPT.ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) .var := rfl

/-- The decryption machine of `prfScheme F E hE hFE` is
`NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) (.const 0)`. -/
theorem prfScheme_dec (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (F n s x)) :
    (prfScheme F E hE hFE).dec =
      NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) (.const 0) := rfl

/-- The encoding of a tuple of ciphertext pairs `(r_j, c_j)_j` as the string handed to a
distinguisher: `encodeList` of the pairs `⟨r_j, c_j⟩`. -/
def encodeTuple {n q : ℕ} (v : Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) : List Bool :=
  PrivateKeyScheme.encodeList (List.ofFn fun j => pairEncode (List.ofFn (v j).1) (List.ofFn (v j).2))

/-- `encodeList l` is the concatenation of the self-delimited chunks `⟨c, []⟩`, `c ∈ l`. -/
private theorem encodeList_eq_flatMap : ∀ l : List (List Bool),
    PrivateKeyScheme.encodeList l = l.flatMap fun c => pairEncode c []
  | [] => by rw [PrivateKeyScheme.encodeList_nil, List.flatMap_nil]
  | c :: l => by
    rw [PrivateKeyScheme.encodeList_cons, List.flatMap_cons, encodeList_eq_flatMap l]
    simp [pairEncode_eq]

/-- The encoded ciphertext tuple is the concatenation of the chunks `⟨⟨r_j, c_j⟩, []⟩` (the
form in which the next-query machine of `MultiMsg.exists_queryChain_nuppt` produces it). -/
theorem encodeTuple_eq_flatten {n q : ℕ} (v : Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) :
    encodeTuple v =
      (List.ofFn fun j =>
        pairEncode (pairEncode (List.ofFn (v j).1) (List.ofFn (v j).2)) []).flatten := by
  rw [encodeTuple, encodeList_eq_flatMap, MultiMsg.flatMap_ofFn]

/-- **The coins of the multi-message experiment of Algorithm 99.1 are bit strings**: the key
coins of `Gen` and the `q + 1` coin strings of `Enc` are `n`-bit strings,
`gen.Coins n × (Fin (q + 1) → enc.Coins n) ≃ {0,1}^n × ({0,1}^n)^{q+1}` (the published coin
identifications `NUPPT.coinsEquiv_ofPolyTimeUniform`; they keep every coin string). -/
noncomputable def prfScheme_coinsEquiv (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x))
    (n q : ℕ) :
    (prfScheme F E hE hFE).gen.Coins n × (Fin (q + 1) → (prfScheme F E hE hFE).enc.Coins n) ≃
      (Fin n → Bool) × (Fin (q + 1) → Fin n → Bool) :=
  (NUPPT.coinsEquiv_ofPolyTimeUniform polyTimeComputable_pairSndD .var n).prodCongr
    (Equiv.piCongrRight fun _ =>
      NUPPT.coinsEquiv_ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) .var n)

/-- The coin equivalence of the multi-message experiment keeps every coin string: the key,
`List.ofFn (prfScheme_coinsEquiv … r).1 = List.ofFn r.1`, and each point,
`List.ofFn ((prfScheme_coinsEquiv … r).2 j) = List.ofFn (r.2 j)`. -/
theorem prfScheme_coinsEquiv_ofFn (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x))
    (n q : ℕ)
    (r : (prfScheme F E hE hFE).gen.Coins n × (Fin (q + 1) → (prfScheme F E hE hFE).enc.Coins n)) :
    List.ofFn (prfScheme_coinsEquiv F E hE hFE n q r).1 = List.ofFn r.1 ∧
      ∀ j, List.ofFn ((prfScheme_coinsEquiv F E hE hFE n q r).2 j) = List.ofFn (r.2 j) :=
  ⟨NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn _ _ n r.1,
    fun j => NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn _ _ n (r.2 j)⟩

/-- **The ciphertext tuple of Algorithm 99.1** is the encoding of the hybrid `H¹`: for the key
`k` and the points `r_j` read off the coins `r` (`prfScheme_coinsEquiv`),
`multiEncDist n q m r = encodeTuple (prfEncReal (F n) m (prfScheme_coinsEquiv … r))`.

**Proof sketch.** `multiEncDist_apply` writes the left side as `encodeList` of the encryptions
`Enc_k(m_j; r_j)`; the key machine outputs its coin string (`runAt_coinKey`) and the encryption
machine outputs `⟨r_j, m_j ⊕ E(⟨k, r_j⟩)⟩` (`runAt_prfEnc`). The coin strings are those of
`prfScheme_coinsEquiv … r` (`prfScheme_coinsEquiv_ofFn`), so `hFE` turns `E(⟨k, r_j⟩)` into
`F n k r_j` and `zipWith_xor_ofFn_add` gives the `j`-th pair of `prfEncReal`. -/
theorem prfScheme_multiEncDist (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x))
    (n q : ℕ) (m : Fin (q + 1) → Fin n → Bool)
    (r : (prfScheme F E hE hFE).gen.Coins n × (Fin (q + 1) → (prfScheme F E hE hFE).enc.Coins n)) :
    (prfScheme F E hE hFE).multiEncDist n q m r =
      encodeTuple (prfEncReal (F n) m (prfScheme_coinsEquiv F E hE hFE n q r)) := by
  rw [PrivateKeyScheme.multiEncDist_apply, encodeTuple]
  congr 1
  congr 1
  funext j
  show (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) .var).runAt n
    (pairEncode ((NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD .var).runAt n [] r.1)
      (List.ofFn (m j))) (r.2 j) = _
  rw [runAt_coinKey, runAt_prfEnc hE]
  have h1 : List.ofFn r.1 = List.ofFn (prfScheme_coinsEquiv F E hE hFE n q r).1 :=
    (prfScheme_coinsEquiv_ofFn F E hE hFE n q r).1.symm
  have h2 : List.ofFn (r.2 j) = List.ofFn ((prfScheme_coinsEquiv F E hE hFE n q r).2 j) :=
    ((prfScheme_coinsEquiv_ofFn F E hE hFE n q r).2 j).symm
  rw [h1, h2, hFE, zipWith_xor_ofFn_add, prfEncReal_apply]

/-- **[PS10, Theorem 99.2]: the scheme of Algorithm 99.1 is multi-message secure** when `F` is
a pseudorandom function family.

**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).

**Proof sketch.** Fix a non-uniform PPT `D` and a budget polynomial `q`. At each `n` choose a
pair of message vectors `(mⁿ, m'ⁿ)` maximizing
`distAdv (multiEncDist n (q n) m) (multiEncDist n (q n) m') (D.distinguisherL n)` over the finite
type of pairs (`Finset.exists_max_image`; the text: "there exists messages `m̄`, `m̄'` … for
infinitely many `n`", hard-wired as advice). *Concrete step:* by `prfScheme_multiEncDist` both
samplers are `encodeTuple ∘ prfEncReal (F n) mⁿ` resp. `m'ⁿ` on the seed space
`K × (Fin (q n + 1) → {0,1}^n)` (the gen coins are the `n`-bit key and the enc coins the points,
definitionally), so with `Dⁿ v c := D.distinguisherL n (encodeTuple v) c` the sunglass identity
`distAdv_comp` and `distAdv_prfEncReal_le` bound the advantage at `n` by
`prfAdv (F n) (multiMsgAdv mⁿ Dⁿ) + prfAdv (F n) (multiMsgAdv m'ⁿ Dⁿ) + 2 · C(q n + 1, 2) / 2^n`
— the six hybrids `H¹, …, H⁶` of the text. *Machine step* (Thm-99.2.1 as an `NUPPT`): for
`v ∈ {m, m'}` the next-query machine `B_v` has advice `⟨encodeList (ofFn (ofFn ∘ vⁿ)), D.advice n⟩`
(`NUPPT.exists_withAdvice`, bound `.add (.mul (.add q (.const 1)) (.add (.mul (.const 2) .var) (.const 2))) D.adv`-style),
coins `(q + 1) · var + D.coins` (`NUPPT.exists_split` with `p := .mul (.add q (.const 1)) .var`: the
first `(q n + 1) n` coins are the points `r₀ … r_{q n}`, read as blocks by
`Complexity.polyTimeComputable_blockMap .var`), and on the encoded history `hist` outputs: if
`|hist| ≤ q n` the query `⟨[false], r_{|hist|}⟩` (history length by `polyTimeComputable_blockMap`
counting, `pairDecode`/`decodeFin` are FP), else the verdict `[true, b]` where `b` is `D`'s
verdict on `encodeTuple (r_j, v_j ⊕ ans_j)_j` (`polyTimeComputable_pairXor` blockwise,
`NUPPT.exists_comp`). By induction on the history, `buildTree` with budget `q n + 1` from `[]`
is the chain `chainTree (q n + 1) r (…)`, i.e.
`B_v.toOracleAdversary n n n (q n + 1) = multiMsgAdv vⁿ Dⁿ` up to the coin bijection
`B_v.Coins n ≃ (Fin (q n + 1) → {0,1}^n) × D.Coins n` (`FunFamily.blocks`, `Fin.appendEquiv`),
so `acceptProb_comp_equiv` gives `prfAdv (F n) (B_v^{(q n + 1)}) = prfAdv (F n) (multiMsgAdv vⁿ Dⁿ)`.
*Asymptotic step:* `hF.negligible_prfAdv B_v (.add q (.const 1))` makes both PRF terms
negligible; the collision term is negligible by `negligible_two_pow_neg` and
`Negligible.mul_pow`/`Negligible.const_mul` with `C(q n + 1, 2) ≤ (q n + 1)^2 ≤ C'(n + 1)^{2d}`
from `PolyExpr.eval_le` (`Nat.choose_le_pow`); `Negligible.add` twice, and by maximality
`ε n := ` this sum bounds the advantage for every `n, m, m'`. -/
theorem prfScheme_multiMessageSecure (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (hF : PRF F) (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x)) :
    (prfScheme F E hE hFE).MultiMessageSecure := by
  refine (PrivateKeyScheme.multiMessageSecure_iff _).2 fun D q => ?_
  -- the worst message pair at each parameter (hard-wired into the reductions)
  have hmax : ∀ n, ∃ p : (Fin (q.eval n + 1) → Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool),
      ∀ w : (Fin (q.eval n + 1) → Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool),
        distAdv ((prfScheme F E hE hFE).multiEncDist n (q.eval n) w.1)
            ((prfScheme F E hE hFE).multiEncDist n (q.eval n) w.2) (D.distinguisherL n) ≤
          distAdv ((prfScheme F E hE hFE).multiEncDist n (q.eval n) p.1)
            ((prfScheme F E hE hFE).multiEncDist n (q.eval n) p.2) (D.distinguisherL n) := by
    intro n
    obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ
      (fun w : (Fin (q.eval n + 1) → Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool) =>
        distAdv ((prfScheme F E hE hFE).multiEncDist n (q.eval n) w.1)
          ((prfScheme F E hE hFE).multiEncDist n (q.eval n) w.2) (D.distinguisherL n))
      Finset.univ_nonempty
    exact ⟨p, fun w => hp w (Finset.mem_univ w)⟩
  choose μ hμ using hmax
  -- the next-query machines of Thm-99.2.1 for the two hard-wired message vectors
  obtain ⟨B₀, hB₀⟩ := MultiMsg.exists_queryChain_nuppt D q fun n => (μ n).1
  obtain ⟨B₁, hB₁⟩ := MultiMsg.exists_queryChain_nuppt D q fun n => (μ n).2
  refine ⟨fun n => prfAdv (F n) (B₀.toOracleAdversary n n n (q.eval n + 1)) +
      prfAdv (F n) (B₁.toOracleAdversary n n n (q.eval n + 1)) +
      2 * ((Nat.choose (q.eval n + 1) 2 : ℝ) / 2 ^ n), ?_, fun n m m' => ?_⟩
  · -- the asymptotic step: two PRF advantages and the collision term
    simpa only [PolyExpr.eval_add, PolyExpr.eval_const] using
      ((hF.negligible_prfAdv B₀ (.add q (.const 1))).add
        (hF.negligible_prfAdv B₁ (.add q (.const 1)))).add
        ((MultiMsg.negligible_choose_div_two_pow q).const_mul 2)
  · refine (hμ n (m, m')).trans ?_
    -- the concrete step: the ciphertext tuples are `encodeTuple ∘ prfEncReal`
    have key : ∀ m₀ : Fin (q.eval n + 1) → Fin n → Bool,
        (prfScheme F E hE hFE).multiEncDist n (q.eval n) m₀ =
          fun r => encodeTuple (prfEncReal (F n) m₀ (prfScheme_coinsEquiv F E hE hFE n (q.eval n) r)) :=
      fun m₀ => funext fun r => prfScheme_multiEncDist F E hE hFE n (q.eval n) m₀ r
    -- the machine step: the oracle adversaries of `B₀`, `B₁` are the `multiMsgAdv`
    have hadv : ∀ (B : NUPPT) (v : Fin (q.eval n + 1) → Fin n → Bool)
        (φ : (Fin (q.eval n + 1) → Fin n → Bool) × D.Coins n ≃ B.Coins n),
        (∀ (g : (Fin n → Bool) → (Fin n → Bool)) ρ c,
          (B.toOracleAdversary n n n (q.eval n + 1) (φ (ρ, c))).eval g =
            decide (D.runAt n (List.ofFn fun j =>
              pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v j + g (ρ j)))) []).flatten c =
                [true])) →
        prfAdv (F n) (B.toOracleAdversary n n n (q.eval n + 1)) =
          prfAdv (F n) (multiMsgAdv v fun w c => D.distinguisherL n (encodeTuple w) c) := by
      intro B v φ hφ
      refine MultiMsg.prfAdv_congr_equiv (F n) _ _ φ fun g w => ?_
      rw [hφ g w.1 w.2, eval_multiMsgAdv, NUPPT.distinguisherL_eq, encodeTuple_eq_flatten]
    obtain ⟨φ₀, hφ₀⟩ := hB₀ n
    obtain ⟨φ₁, hφ₁⟩ := hB₁ n
    dsimp only
    rw [hadv B₀ (μ n).1 φ₀ hφ₀, hadv B₁ (μ n).2 φ₁ hφ₁, key, key, distAdv_def,
      acceptProb_comp_equiv (prfScheme_coinsEquiv F E hE hFE n (q.eval n))
        (fun s => encodeTuple (prfEncReal (F n) (μ n).1 s)),
      acceptProb_comp_equiv (prfScheme_coinsEquiv F E hE hFE n (q.eval n))
        (fun s => encodeTuple (prfEncReal (F n) (μ n).2 s)), ← distAdv_def]
    exact (distAdv_comp encodeTuple (prfEncReal (F n) (μ n).1) (prfEncReal (F n) (μ n).2)
      (D.distinguisherL n)).symm.trans_le (distAdv_prfEncReal_le (F n) (μ n).1 (μ n).2
        (fun w c => D.distinguisherL n (encodeTuple w) c))

/-- **Multi-message secure private-key encryption exists if a PRF exists** ([PS10, §3.9]):
the scheme of Algorithm 99.1 with the evaluator of `PRF.easy`. -/
theorem exists_multiMessageSecure_of_prf {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)}
    (hF : PRF F) : ∃ S : PrivateKeyScheme, S.MultiMessageSecure :=
  let ⟨E, hE, hFE⟩ := hF.easy
  ⟨prfScheme F E hE hFE, prfScheme_multiMessageSecure F hF E hE hFE⟩

/-- **Multi-message secure private-key encryption exists if a PRG exists** ([PS10, Theorems
97.3 and 99.2] combined): GGM gives a PRF, Algorithm 99.1 gives the scheme. -/
theorem exists_multiMessageSecure_of_exists_prg (h : ∃ P : PRG, P.Secure) :
    ∃ S : PrivateKeyScheme, S.MultiMessageSecure :=
  let ⟨_, hF⟩ := exists_prf_of_exists_prg h
  exists_multiMessageSecure_of_prf hF

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF
import Mathlib.Tactic.Simps.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The §3.9 scheme under chosen-plaintext and chosen-ciphertext attacks (statement phase)

[PS10, Theorem 168.2]: the scheme of Algorithm 99.1 (the ch. 2–4 layer's `prfScheme`:
`Enc_k(m) = ⟨r, m ⊕ f_k(r)⟩` for a fresh uniform `r`) is CPA- and CCA1-secure when `F` is a PRF.
[PS10, §7.1.3, Claim 169.a in the inventory]: it is not CCA2-secure, whatever `F`.

The CCA1 statement relies on `Dec` refusing malformed ciphertexts (`prfDecWF`): the evaluator `E`
agrees with `F` only on `⟨s, x⟩` with `|s| = |x|`, and a decryption query must not reach it
elsewhere.

## Main definitions

* `Composability.prfFixedScheme`: `prfScheme`, whose ciphertexts have `3n + 2` bits.

## Main results

* `Composability.prfFixedScheme_cpa`, `Composability.prfFixedScheme_cca1` (Thm 168.2, stated;
  `sorry`s under the source's sketch).
* `Composability.prfFixedScheme_not_cca2` (Claim 169.a, proved): an explicit adversary with
  advantage `1`.
* `Composability.not_prfFixedScheme_cca2`: hence the scheme is not CCA2-secure (proved from the
  claim).

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

/-- **Theorem 168.2 (CPA)** [PS10]: if `F` is a pseudorandom function family, the §3.9 scheme is
CPA-secure.

**Proof sketch** (the source's).
1. Replace `f_k` by a random function: by PRF security, the advantage changes by a negligible
   amount (the reduction answers `Enc` and the challenge by querying its own oracle at the fresh
   `r`). T2 (`Games.exists_interactiveHandlerMachine`) implements this forwarding handler,
   with the challenge bit in the seed and a finalization that compares the guess with that
   bit; the input-free companion and T4 (`Games.exists_toOracleAdversary_of_bitCodec`)
   supply the oracle adversary used by `OracleEnsemble.Indist`.
2. With a random function, the challenge's pad `RF(r*)` is uniform and independent of everything
   else unless `r*` collides with the `r` of some `Enc` answer. A collision has probability at most
   `q(n) / 2^n` (the collision bound `prob_mem_le`, one fresh draw against at most `q` earlier
   ones).
3. Off the collision, `m_b ⊕ RF(r*)` is uniform for both `b` (identical until bad,
   `identical_until_bad`), so the advantage is at most `q(n)/2^n` plus the PRF advantage:
   negligible. -/
theorem prfFixedScheme_cpa (hF : PRF F) : (prfFixedScheme F E hE hFE).INDSecure .cpa := by
  sorry

/-- **Theorem 168.2 (CCA1)** [PS10]: if `F` is a pseudorandom function family, the §3.9 scheme
is CCA1-secure.

**Proof sketch** (the source's). As for CPA, with the reduction also answering decryption
queries before the challenge with its oracle (`Dec_k(⟨r, c⟩) = c ⊕ f_k(r)` on well-formed
ciphertexts, `runAt_prfDec`; `⊥` on the others, `decodeFin_runAt_prfDec_of_not_wf`). The bad event
adds the case that a pre-challenge decryption query used the challenge's `r*`, again at most
`q(n)/2^n`, because `r*` is drawn after those queries. -/
theorem prfFixedScheme_cca1 (hF : PRF F) : (prfFixedScheme F E hE hFE).INDSecure .cca1 := by
  sorry

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
the pair of that nonce and the message masked by `F n k x`. -/
private theorem cca2Encrypt (n : ℕ) (k m : Fin n → Bool)
    (r : (prfFixedScheme F E hE hFE).enc.Coins n) :
    ∃ x : Fin n → Bool, List.ofFn r = List.ofFn x ∧
      List.ofFn ((prfFixedScheme F E hE hFE).encryptAt n (List.ofFn k) m r) =
        pairEncode (List.ofFn x) (List.ofFn (m + F n k x)) := by
  revert r
  simp only [FixedLengthScheme.encryptAt_eq, prfFixedScheme_ctLen]
  rw [prfFixedScheme_enc, prfScheme_enc]
  intro r
  let x := NUPPT.coinsEquiv_ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) .var n r
  have hx : List.ofFn x = List.ofFn r :=
    NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn _ _ n r
  refine ⟨x, hx.symm, ?_⟩
  rw [runAt_prfEnc hE, ← hx, hFE, zipWith_xor_ofFn_add]
  apply GGMRed.ofFn_padFin_of_length
  simp only [length_pairEncode, List.length_ofFn, PolyExpr.eval_add,
    PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  omega

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
  apply GGMRed.ofFn_padFin_of_length
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

/-- The ciphertext width evaluates to `3 * n + 2`. -/
private theorem cca2CtLen (n : ℕ) :
    (prfFixedScheme F E hE hFE).ctLen.eval n = 3 * n + 2 := by
  rw [prfFixedScheme_ctLen, PolyExpr.eval_add, PolyExpr.eval_mul,
    PolyExpr.eval_const, PolyExpr.eval_const, PolyExpr.eval_var]

/-- Every generated key is an `n`-bit word. -/
private theorem cca2Gen (n : ℕ) (rg : (prfFixedScheme F E hE hFE).gen.Coins n) :
    ∃ k : Fin n → Bool, (prfFixedScheme F E hE hFE).gen.runAt n [] rg = List.ofFn k := by
  revert rg
  rw [prfFixedScheme_gen, prfScheme_gen]
  intro rg
  rw [runAt_coinKey]
  exact ⟨NUPPT.coinsEquiv_ofPolyTimeUniform polyTimeComputable_pairSndD .var n rg,
    (NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn _ _ n rg).symm⟩

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
    rw [cca2CtLen]
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

/-- Transporting a bit vector along a width equality does not change its word:
`List.ofFn (cast h f) = List.ofFn f` when `h` comes from `a = b`. -/
private theorem cca2OfFn_cast {a b : ℕ} (hab : a = b) (h : (Fin a → Bool) = (Fin b → Bool))
    (f : Fin a → Bool) : List.ofFn (cast h f) = List.ofFn f := by
  subst hab
  rfl

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
      rw [hx, cca2OfFn_cast (S.inLens_two n).symm, cca2Messages_ofFn]
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
    rw [cca2OfFn_cast (S.outLens_two n).symm, ← cca2Alter_ofFn hd,
      ← cca2OfFn_cast (S.inLens_one n).symm (S.indSpec_decDom n).symm]
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
    rw [cca2OfFn_cast (S.outLens_one n).symm, hlast, Bool.not_not]
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
    rw [cca2CtLen]
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

## ===== TCSlib/Cryptography/Encryption/PrivateKey/OracleSecurity.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Cryptography.Games.Advantage
import TCSlib.Cryptography.Encryption.PrivateKey.Scheme
import TCSlib.Cryptography.Foundations.Negligible

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# CPA, CCA1 and CCA2 security of private-key encryption (definitions)

[PS10, Definition 168.1], the first definition of ch. 7 (prong C of the ch. 5–8 campaign), stated
as a game of the `Games` framework over the ch. 2–4 layer's `PrivateKeyScheme`.

**The experiment** `IND_b^{O₁,O₂}(Π, A, n)`: `k ← Gen(1^n)`; `(m₀, m₁, state) ← A^{O₁(k)}(1^n)`;
`c ← Enc_k(m_b)`; output `A^{O₂(k)}(c, state)`. The oracle pairs are `[Enc; Enc]` (CPA),
`[Enc, Dec; Enc]` (CCA1) and `[Enc, Dec; Enc, Dec]` (CCA2). Under CCA2, `Dec` returns `⊥` on the
challenge `c`.

**Its encoding.** One machine plays both phases against three bit-string oracles:
- `Enc` (`n`-bit messages, `ct(n)`-bit ciphertexts);
- `Dec` (`ct(n)`-bit ciphertexts; an `(n + 1)`-bit answer, a validity flag followed by the message);
- `Challenge`, which takes `⟨m₀, m₁⟩` and returns `c ← Enc_k(m_b)`.

The oracles' state remembers the challenge, once asked. That state decides the phase: `Dec` answers
never (CPA), before the challenge only (CCA1), or always, except on `c` itself (CCA2). A refused
`Dec` query, or a repeated challenge, gets a fixed answer. The machine's final output is one bit.

**Deviations, declared once here.**
- **One machine for both phases.** The source's two-phase adversary passes `state` from phase 1
  to phase 2. Here a single next-move machine plays both phases, and its query log (which includes
  the challenge `c`) is that state. Either form simulates the other, at polynomial cost.
- **Fixed-length ciphertexts.** The scheme's ciphertexts at parameter `n` have exactly `ct(n)`
  bits (`FixedLengthScheme`), as the oracle codec needs.
- **Query budgets.** The adversary's number of oracle queries is an explicit polynomial `q`,
  universally quantified, as in the ch. 2–4 layer's `OracleEnsemble.Indist`.
- **Indistinguishability** of the two one-bit outputs is a negligible distinguishing advantage
  between the games for `b = 0` and `b = 1`.

## Main definitions

* `Composability.Attack`: CPA, CCA1, CCA2.
* `Composability.FixedLengthScheme`: a `PrivateKeyScheme` with fixed-length ciphertexts.
* `FixedLengthScheme.indImpl`, `FixedLengthScheme.indGame`: the oracles and the experiment
  `IND_b`.
* `FixedLengthScheme.INDSecure`: [PS10, Definition 168.1].

## Main results

* `indImpl_dec_cpa`, `indImpl_dec_cca2_challenge`, `indImpl_challenge_repeat`: sanity checks of
  the oracles (CPA's `Dec` is closed; CCA2's `Dec` refuses the challenge; a challenge is asked
  once).

The theorems on these notions (Thms 168.2 and 170.4, Claim 169.a) are stated in the statement
phase of prong C, in their own modules.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.1.1, Definition 168.1 (book p. 168).
-/

namespace TCSlib.Cryptography.Composability

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-- The three attacks of [PS10, Definition 168.1]. -/
inductive Attack : Type where
  /-- Chosen-plaintext: `[Enc; Enc]`. -/
  | cpa
  /-- Non-adaptive chosen-ciphertext: `[Enc, Dec; Enc]`. -/
  | cca1
  /-- Adaptive chosen-ciphertext: `[Enc, Dec; Enc, Dec]`, `Dec` refusing the challenge. -/
  | cca2
  deriving DecidableEq

/-- A **private-key encryption scheme with fixed-length ciphertexts**: every encryption of an
`n`-bit message under a generated key has exactly `ct(n)` bits. -/
structure FixedLengthScheme extends PrivateKeyScheme where
  /-- The ciphertext length `ct(n)`. -/
  ctLen : PolyExpr
  /-- Ciphertexts of `n`-bit messages under generated keys have `ct(n)` bits. -/
  enc_length : ∀ n (rg : gen.Coins n) (m : Fin n → Bool) (r : enc.Coins n),
    (enc.runAt n (pairEncode (gen.runAt n [] rg) (List.ofFn m)) r).length = ctLen.eval n

namespace FixedLengthScheme

variable (S : FixedLengthScheme)

/-- The query lengths of the three oracles `Enc`, `Dec`, `Challenge` at parameter `n`. -/
def inLens (n : ℕ) : Fin 3 → ℕ
  | 0 => n
  | 1 => S.ctLen.eval n
  | 2 => n + n

/-- The encryption oracle accepts `n`-bit messages. -/
theorem inLens_zero (n : ℕ) : S.inLens n 0 = n := rfl

/-- The decryption oracle accepts ciphertexts of the fixed ciphertext length. -/
theorem inLens_one (n : ℕ) : S.inLens n 1 = S.ctLen.eval n := rfl

/-- The challenge oracle accepts a pair of `n`-bit messages. -/
theorem inLens_two (n : ℕ) : S.inLens n 2 = n + n := rfl

/-- The answer lengths of the three oracles at parameter `n`; `Dec`'s answer is a validity flag
followed by the message. -/
def outLens (n : ℕ) : Fin 3 → ℕ
  | 0 => S.ctLen.eval n
  | 1 => n + 1
  | 2 => S.ctLen.eval n

/-- Encryption returns the fixed ciphertext length. -/
theorem outLens_zero (n : ℕ) : S.outLens n 0 = S.ctLen.eval n := rfl

/-- Decryption returns a validity bit followed by an `n`-bit message. -/
theorem outLens_one (n : ℕ) : S.outLens n 1 = n + 1 := rfl

/-- The challenge returns the fixed ciphertext length. -/
theorem outLens_two (n : ℕ) : S.outLens n 2 = S.ctLen.eval n := rfl

/-- The three oracles of the experiment at parameter `n`. -/
abbrev indSpec (n : ℕ) : OracleSpec (Fin 3) := bitSpec (S.inLens n) (S.outLens n)

/-- The IND oracle specification has the published input and output lengths. -/
theorem indSpec_eq (n : ℕ) : S.indSpec n = bitSpec (S.inLens n) (S.outLens n) := rfl

/-- Whether `Dec` answers, given the attack and whether the challenge has been asked. -/
def decOpen : Attack → Bool → Bool
  | .cpa, _ => false
  | .cca1, challenged => !challenged
  | .cca2, _ => true

/-- CPA never opens the decryption oracle. -/
theorem decOpen_cpa (challenged : Bool) : decOpen .cpa challenged = false := rfl

/-- CCA1 opens decryption exactly before the challenge. -/
theorem decOpen_cca1 (challenged : Bool) : decOpen .cca1 challenged = !challenged := rfl

/-- CCA2 always opens decryption, with the challenge refusal checked separately. -/
theorem decOpen_cca2 (challenged : Bool) : decOpen .cca2 challenged = true := rfl

/-- The ciphertext `Enc_k(m)` with coins `r`, read at `ct(n)` bits. -/
def encryptAt (n : ℕ) (k : List Bool) (m : Fin n → Bool) (r : S.enc.Coins n) :
    Fin (S.ctLen.eval n) → Bool :=
  padFin _ (S.enc.runAt n (pairEncode k (List.ofFn m)) r)

/-- Encryption is the padded reading of the underlying encryption machine's output. -/
theorem encryptAt_eq (n : ℕ) (k : List Bool) (m : Fin n → Bool) (r : S.enc.Coins n) :
    S.encryptAt n k m r = padFin (S.ctLen.eval n)
      (S.enc.runAt n (pairEncode k (List.ofFn m)) r) := rfl

/-- `Dec`'s answer `⟨1, m⟩` on a valid decryption `m`, and the all-`false` `⊥` otherwise. -/
def decAnswer {n : ℕ} : Option (Fin n → Bool) → (Fin (n + 1) → Bool)
  | some m => Fin.cons (α := fun _ => Bool) true m
  | none => zeroBits _

/-- A successful decryption is prefixed by its `true` validity bit. -/
theorem decAnswer_some {n : ℕ} (m : Fin n → Bool) :
    decAnswer (some m) = Fin.cons (α := fun _ => Bool) true m := rfl

/-- Failed decryption is the all-false answer. -/
theorem decAnswer_none (n : ℕ) : decAnswer (n := n) none = zeroBits (n + 1) := rfl

/-- The first and the second `n` bits of a `2n`-bit query: the challenge messages `m₀, m₁`. -/
def splitHalf {n : ℕ} (x : Fin (n + n) → Bool) : (Fin n → Bool) × (Fin n → Bool) :=
  (fun i => x (Fin.castAdd n i), fun j => x (Fin.natAdd n j))

/-- The first half of a challenge query consists of its first `n` bits. -/
theorem splitHalf_fst {n : ℕ} (x : Fin (n + n) → Bool) :
    (splitHalf x).1 = fun i => x (Fin.castAdd n i) := rfl

/-- The second half of a challenge query consists of its final `n` bits. -/
theorem splitHalf_snd {n : ℕ} (x : Fin (n + n) → Bool) :
    (splitHalf x).2 = fun j => x (Fin.natAdd n j) := rfl

/-- **The oracles of `IND_b`** at parameter `n`, for the key `k`; the state is the challenge,
once asked.
- `Enc` answers `Enc_k(m)` with fresh coins.
- `Dec` answers `⟨1, Dec_k(c)⟩` with fresh coins when it is open (`decOpen`) and `c` is not the
  challenge, and `⊥` (all `false`) otherwise; a ciphertext that fails to decrypt is `⊥` as well.
- `Challenge` answers `Enc_k(m_b)` on `⟨m₀, m₁⟩` the first time it is asked, and records it;
  later it repeats the recorded challenge. -/
noncomputable def indImpl (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool) :
    QueryImpl (S.indSpec n) (Option (Fin (S.ctLen.eval n) → Bool)) unifSpec
  | 0, m, s => (ProbComp.sample (S.enc.Coins n)).bind fun r => .pure (S.encryptAt n k m r, s)
  | 1, c, s =>
    if decOpen atk s.isSome && !decide (s = some c) then
      (ProbComp.sample (S.dec.Coins n)).bind fun r =>
        .pure (decAnswer (decodeFin n (S.dec.runAt n (pairEncode k (List.ofFn c)) r)), s)
    else .pure (zeroBits _, s)
  | 2, mm, s =>
    match s with
    | some c => .pure (c, s)
    | none =>
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let c := S.encryptAt n k (if b then (splitHalf mm).2 else (splitHalf mm).1) r
        .pure (c, some c)

/-- An encryption query samples fresh encryption coins and preserves the challenge state. -/
theorem indImpl_enc (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (m : Fin n → Bool) (st : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl atk b n k 0 m st =
      (ProbComp.sample (S.enc.Coins n)).bind fun r => .pure (S.encryptAt n k m r, st) := rfl

/-- Decryption queries test oracle availability and refuse the recorded challenge before
running the decryption machine. -/
theorem indImpl_dec (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (c : Fin (S.ctLen.eval n) → Bool) (st : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl atk b n k 1 c st =
      if decOpen atk st.isSome && !decide (st = some c) then
        (ProbComp.sample (S.dec.Coins n)).bind fun r =>
          .pure (decAnswer (decodeFin n (S.dec.runAt n (pairEncode k (List.ofFn c)) r)), st)
      else .pure (zeroBits _, st) := rfl

/-- A first challenge query encrypts the selected half and records that ciphertext. -/
theorem indImpl_challenge_none (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (mm : Fin (n + n) → Bool) :
    S.indImpl atk b n k 2 mm none =
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let c := S.encryptAt n k (if b then (splitHalf mm).2 else (splitHalf mm).1) r
        .pure (c, some c) := rfl

/-- Under CPA, `Dec` never answers: every decryption query gets `⊥`. -/
theorem indImpl_dec_cpa (b : Bool) (n : ℕ) (k : List Bool)
    (c : Fin (S.ctLen.eval n) → Bool) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl .cpa b n k 1 c s = .pure (zeroBits _, s) := by
  simp [indImpl, decOpen]

/-- Under CCA2, `Dec` refuses the challenge: on the recorded challenge `c` it answers `⊥`. -/
theorem indImpl_dec_cca2_challenge (b : Bool) (n : ℕ) (k : List Bool)
    (c : Fin (S.ctLen.eval n) → Bool) :
    S.indImpl .cca2 b n k 1 c (some c) = .pure (zeroBits _, some c) := by
  simp [indImpl, decOpen]

/-- A repeated challenge query returns the recorded challenge and changes nothing. -/
theorem indImpl_challenge_repeat (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (mm : Fin (n + n) → Bool) (c : Fin (S.ctLen.eval n) → Bool) :
    S.indImpl atk b n k 2 mm (some c) = .pure (c, some c) := rfl

/-- The decryption oracle accepts a ciphertext at the fixed ciphertext width:
`(S.indSpec n).dom 1 = (Fin (S.ctLen.eval n) → Bool)`. -/
theorem indSpec_decDom (n : ℕ) : (S.indSpec n).dom 1 = (Fin (S.ctLen.eval n) → Bool) := by
  rw [S.indSpec_eq, bitSpec_dom, S.inLens_one]

/-- The decryption oracle answers a validity bit followed by an `n`-bit message:
`(S.indSpec n).rng 1 = (Fin (n + 1) → Bool)`. -/
theorem indSpec_decRng (n : ℕ) : (S.indSpec n).rng 1 = (Fin (n + 1) → Bool) := by
  rw [S.indSpec_eq, bitSpec_rng, S.outLens_one]

/-- A challenge query contains two `n`-bit messages:
`(S.indSpec n).dom 2 = (Fin (n + n) → Bool)`. -/
theorem indSpec_challengeDom (n : ℕ) : (S.indSpec n).dom 2 = (Fin (n + n) → Bool) := by
  rw [S.indSpec_eq, bitSpec_dom, S.inLens_two]

/-- The challenge oracle answers a ciphertext at the fixed ciphertext width:
`(S.indSpec n).rng 2 = (Fin (S.ctLen.eval n) → Bool)`. -/
theorem indSpec_challengeRng (n : ℕ) : (S.indSpec n).rng 2 = (Fin (S.ctLen.eval n) → Bool) := by
  rw [S.indSpec_eq, bitSpec_rng, S.outLens_two]

/-- The decryption equation on the query specification's type: with `c' = cast _ c` the
ciphertext read at width `ct(n)`, `S.indImpl atk b n k 1 c st` is
`if decOpen atk st.isSome && !decide (st = some c')` then a fresh `r ← Dec.Coins n` and the answer
`cast _ (decAnswer (decodeFin n (Dec.runAt n ⟨k, c'⟩ r)))` with state `st`, else `⊥` with `st`. -/
theorem indImpl_dec_onSpec (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (c : (S.indSpec n).dom 1) (st : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl atk b n k 1 c st =
      if decOpen atk st.isSome && !decide (st = some (cast (S.indSpec_decDom n) c)) then
        (ProbComp.sample (S.dec.Coins n)).bind fun r =>
          .pure (cast (S.indSpec_decRng n).symm (decAnswer (decodeFin n
            (S.dec.runAt n (pairEncode k (List.ofFn (cast (S.indSpec_decDom n) c))) r))), st)
      else .pure (zeroBits _, st) := by
  simpa only [cast_eq] using S.indImpl_dec atk b n k c st

/-- The fresh challenge equation on the query specification's type: with
`⟨m₀, m₁⟩ = splitHalf (cast _ mm)`, `S.indImpl atk b n k 2 mm none` draws `r ← Enc.Coins n`,
sets `c = S.encryptAt n k m_b r`, and returns `cast _ c` with the state `some c`. -/
theorem indImpl_challenge_none_onSpec (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (mm : (S.indSpec n).dom 2) :
    S.indImpl atk b n k 2 mm none =
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let halves := splitHalf (cast (S.indSpec_challengeDom n) mm)
        let c := S.encryptAt n k (if b then halves.2 else halves.1) r
        .pure (cast (S.indSpec_challengeRng n).symm c, some c) := by
  simpa only [cast_eq] using S.indImpl_challenge_none atk b n k mm

/-- The codec of the adversary: the three oracles, and a one-bit final output. -/
def indCodec (n : ℕ) : MachineCodec (S.indSpec n) (Fin 1 → Bool) :=
  bitCodec (S.inLens n) (S.outLens n) 1

/-- The IND codec decodes a move using the bit-string decoder at its oracle lengths. -/
theorem indCodec_decodeMove (n : ℕ) (w : List Bool) :
    (S.indCodec n).decodeMove w = decodeBitMove (S.inLens n) (S.outLens n) 1 w :=
  bitCodec_decodeMove (S.inLens n) (S.outLens n) 1 w

/-- The IND codec records a log entry as the oracle index paired with its query and answer. -/
theorem indCodec_encodeEntry (n : ℕ)
    (e : Σ i, (S.indSpec n).dom i × (S.indSpec n).rng i) :
    (S.indCodec n).encodeEntry e =
      pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)) :=
  bitCodec_encodeEntry (S.inLens n) (S.outLens n) 1 e

/-- The IND codec returns the false verdict when its budget expires. -/
theorem indCodec_timeout (n : ℕ) : (S.indCodec n).timeout = zeroBits 1 :=
  bitCodec_timeout (S.inLens n) (S.outLens n) 1

/-- **The experiment `IND_b^{O₁,O₂}(Π, A, n)`** [PS10, Definition 168.1] for the attack `atk`, with
query budget `q`: sample `k ← Gen(1^n)` and `A`'s coins, run `A` against the oracles of `IND_b`
from the unchallenged state, and output its bit. -/
noncomputable def indGame (atk : Attack) (A : NUPPT) (q : ℕ) (b : Bool) (n : ℕ) : ProbComp Bool :=
  (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (A.Coins n)).bind fun r =>
  (simulate (S.indImpl atk b n (S.gen.runAt n [] rg)) (A.toComp (S.indCodec n) n q r) none).bind
    fun res => .pure (res.1 0)

/-- The IND experiment samples keys and adversary coins, simulates the recorded oracle
interaction from the unchallenged state, and returns the final bit. -/
theorem indGame_eq (atk : Attack) (A : NUPPT) (q : ℕ) (b : Bool) (n : ℕ) :
    S.indGame atk A q b n =
      (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
      (ProbComp.sample (A.Coins n)).bind fun r =>
      (simulate (S.indImpl atk b n (S.gen.runAt n [] rg))
        (A.toComp (S.indCodec n) n q r) none).bind fun res => .pure (res.1 0) := rfl

/-- **CPA, CCA1 or CCA2 security** [PS10, Definition 168.1]: for every non-uniform PPT `A` and
every polynomial query budget, `IND_0` and `IND_1` are indistinguishable: `A`'s advantage between
them is negligible. -/
def INDSecure (atk : Attack) : Prop :=
  ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n, advantage (S.indGame atk A (q.eval n) false n) (S.indGame atk A (q.eval n) true n) ≤ ε n

/-- IND security is exactly negligible advantage for every PPT adversary and polynomial
query budget, uniformly over the security parameter. -/
theorem INDSecure_iff (atk : Attack) :
    S.INDSecure atk ↔ ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n, advantage (S.indGame atk A (q.eval n) false n)
        (S.indGame atk A (q.eval n) true n) ≤ ε n := Iff.rfl

end FixedLengthScheme

end TCSlib.Cryptography.Composability
