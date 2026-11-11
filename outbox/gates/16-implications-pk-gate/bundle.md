## ===== briefs/pass-shelat-ch5-8/gates/16-implications-pk/pack.md =====

# Gate 16 · Implications: public-key encryption from RSA and from factoring

Round 1. Auditor Codex. Seyoon ruled on 2026-11-11 that RSA and Rabin go in one PR with one Codex audit.

- **PR:** draft [PR #292](https://github.com/Shilun-Allan-Li/tcslib/pull/292) at
  `33a616bcc14450b9e3110e4f8801abea1198b2fb` (branch `maint/pass-shelat-implications-pk`).
- **Target and base:** it targets `cryptography/pass-shelat-ch2-4` on base
  `33cb7ae74c8e6ac23ed5bb1875121eadfe0c2046`, the campaign after #291; later base commits are records only.
- **What it adds:** a new catalog layer, `TCSlib/Cryptography/Implications` (facade exported from
  `TCSlib.lean`), and its first module, `Implications/PublicKey.lean`.
- **Scope:** this is a combined statement and proof audit. The proofs are four-line compositions of published
  theorems.

## The two catalog entries

```lean
theorem exists_adaptiveCPA_of_rsa (H : ArithmeticFP) (hR : RSAAssumption) :
    ∃ S : FixedLengthPKScheme, S.msgLen = .var ∧ S.AdaptiveINDSecure .cpa

theorem exists_adaptiveCPA_of_factoring (H : ArithmeticFP) (hD : BlumDensity)
    (hF : FactoringAssumption) :
    ∃ S : FixedLengthPKScheme, S.msgLen = .var ∧ S.AdaptiveINDSecure .cpa
```

The source is [PS10], R. Pass and a. shelat, *A Course in Cryptography*, third edition, January 2010. The
relevant results are Theorems 53.2 and 57.2 (RSA), §2.12 and Theorems 61.8 and 63.10 (Rabin–Blum), Theorem 87.3
(Goldreich–Levin), Algorithm 104.3 and Theorem 104.4, the bitwise scheme of p. 103, and Definition 171.5.

## What to check

1. **Statements.**
   - Is each statement the right catalog endpoint per the Implications design (`implications/README.md`, in the
     bundle)? That means: a full, explicit assumption set; a meaningful message space; and the exact audited game.
   - Are all premises present? In particular:
     - `ArithmeticFP` is the arithmetic efficiency premise.
     - `BlumDensity` stays a hypothesis.
     - No hidden admission enters through a callee.
   - Does `FixedLengthPKScheme` carry the guarantees the module docstring claims?
     - uniform polynomial-time key generation and encryption;
     - polynomial-time decryption;
     - fixed-length ciphertexts;
     - perfect correctness.
   - Is `msgLen = .var` enough to rule out a vacuous witness?
2. **Proofs.** Each composes four published results:
   - `rsaTrapdoor_oneWay` / `rabinBlumTrapdoor_oneWay`;
   - `TrapdoorCollection.shiftParameter_oneWay`, shifting by 2 / 3;
   - `TrapdoorCollection.OneWay.exists_glPad_singleBitSecure`, with
     `rsaTrapdoor_shiftParameter_encD_length` / `rabinBlumTrapdoor_shiftParameter_encD_length` as the
     exact-width premise `henc`;
   - `BitPublicKeyScheme.SingleBitSecure.exists_adaptive_cpa`.

   Confirm the composition is sound, and that the shift does not weaken the guarantee: the scheme's
   parameter `n` is the security parameter of the adaptive game.
3. **Axioms.** Both theorems must print only `propext`, `Classical.choice` and `Quot.sound`. Inspect the full
   dependency chain, not just the wrapper: the design notes warn that a wrapper with no local `sorry` is not
   enough.
4. **Layering.** Implications imports construction modules, and nothing imports Implications except the root.
   Check the module and facade docstrings (`## Contents`, references), the namespace
   `Implications.PublicKey`, and that there is no `@[simp]`. The design notes' instruction not to publish RSA or
   Rabin wrappers "with the current impossible `henc` premise" is now met: `henc` is proved at the shifted
   parameters.
5. **Rule 10.** The proofs name only theorems. The seal probe re-elaborates both proofs with the main
   definitions sealed, together with a control.

## Evidence (`evidence/`)

- `build.jsonl`, `build-order.txt`: `Implications/PublicKey`, the facade and `TCSlib` pass with rc 0, 0 errors
  and no warnings. Each row records the source SHA-256, which matches `source-head.json`.
- `SealProbe.lean`, `seal-probe.log`: both proofs elaborate with `rsaTrapdoor`, `rabinBlumTrapdoor`,
  `shiftParameter`, `glPad`, `tdpBitScheme`, `SingleBitSecure`, `bitwise`, `padded`, `AdaptiveINDSecure`,
  `RSAAssumption`, `FactoringAssumption` and `BlumDensity` sealed. The only error is the intended control at
  line 33. The probe's `#print axioms` lines give the standard axioms.
- `screen-axioms.log`: the original composition screen.

## Findings delivery

Return `gate16-implications-pk-findings.md` as a Markdown file in this chat. For multiple evidence files, return a
ZIP. The user dispatches and merges.

| # | Severity | File and declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

Severities:
- **blocker:** a false or unusable statement, or a scope violation.
- **major:** a missing premise, a vacuous or misleading endpoint, a hidden admission, a forbidden read, or
  necessary evidence that cannot be verified.
- **minor:** documentation or API defects.
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

## ===== briefs/pass-shelat-ch5-8/implications/README.md =====

# Implications layer — campaign work item I1

**Authorized by Seyoon Ragavan, 2026-11-07 PST. Drafting, not issued for an external job.**

Collect, by cryptographic primitive, the end results of the library's construction chains:
an explicit set of hardness assumptions jointly implies existence of a fundamental primitive
with a precise security notion. A first-class entry is a final implication, not every step of
its construction chain (user clarification, 2026-11-07 PST).
Keep the proofs short applications of the existing results. The user requested this after
tracing RSA to public-key encryption and observing the uncomposed encoding bridge.

## Proposed layout

- `TCSlib/Cryptography/Implications.lean`: facade, exported from `TCSlib.lean`.
- `Implications/PublicKey.lean`: first pilot. The user-selected catalog endpoints are multi-message
  IND-CPA PKE and multi-message IND-CCA2 PKE (2026-11-07 PST). CCA1 is a documented intermediate.
  Existing single-bit, hard-core-TDP, bitwise and security-lifting lemmas stay supporting APIs.
- Later coherent modules for pseudorandomness/private-key encryption, authentication,
  commitments/zero knowledge, and oblivious transfer. Split by primitive as contents grow;
  this is an output-facing composition layer, above candidate and construction modules.

Dependencies point toward Implications. Definitions, candidate modules and reduction modules
never import it. The short proofs cite their public APIs and preserve every cost, domain,
length and auxiliary hardness hypothesis. Thin compositions through existing APIs need no new host. Precise multi-message target
predicates and model conversions still require design where the existing APIs do not express
the selected guarantee.

## Admission to the catalog

A result belongs here when it connects a useful, explicitly stated assumption set to a
fundamental primitive. Include all computational infrastructure, domain, length, correctness
and auxiliary hardness premises in its header. Several independent assumption sets may have
theorems with the same endpoint. Intermediate constructions and automatic weaker guarantees
are indexed through links, rather than promoted into parallel catalog entries.

The PKE target must support a meaningful message space (for example n-bit messages with a
proved extension), so an existential cannot be witnessed by an empty-message-only scheme.
Multi-message security is part of the intended endpoint, with the exact experiment stated;
it is not a separate primitive category. No source-level single-message claim is silently
relabelled as an adaptive multi-challenge game.

## Contents and status

`public-key-draft.md` gives proposed statements, proof terms, existing source locations and
blockers. `normalization-design.md` records a constant-shift route to the concrete RSA/Rabin
width bridge, with the missing transports explicit and no checked-proof claim. `inventory-draft.md` surveys 13 primitive families and their exact endpoints, retained premises, admissions and missing bridges. The first source survey is against
campaign records/source `f3c7958506bd258863a0adf93e4cc0aa3183336e`. The four Gate 06 statement
gates later closed and their headers landed in [#232](https://github.com/Shilun-Allan-Li/tcslib/pull/232).
The design notes retain source locations from their survey. Use the current plan
for the relocated owners, remaining proofs, and endpoint sequence.

A result index records assumption, precise conclusion, implementation theorem, hypotheses,
source reference, gate/fill status and remaining bridge. A source `sorry` count of zero in a
wrapper is insufficient: inspect its full axiom dependency set and the status of its callees.

Do not publish RSA/Rabin existence wrappers with the current impossible `henc` premise. Keep
those chains as blocked index rows until their real normalization/padding bridge is available.
Likewise, ElGamal's GroupPKScheme security is not silently a theorem about the other PKE types.

## Execution

The [proof and Implications plan](../PROOFS-AND-IMPLICATIONS-PLAN.md) sequences
the shared reduction proofs, the CPA pilot, and the later CCA2 construction.
Thin compositions through checked APIs are maintainer PR work. New
interfaces and model transports follow the statement gate and proof process.

**Not yet clear to merge — contents are a draft; no Implications Lean PR exists yet.**

## ===== briefs/pass-shelat-ch5-8/implications/public-key-draft.md =====

# Public-key implications pilot — proposed contents

**Draft, 2026-11-07 PST.** Names below are proposals, not declarations claimed to exist.
Proof snippets are source-level drafts and have not been elaborated as a new module.

## First-class endpoints — selected by the user, 2026-11-07 PST

| Endpoint | Intended guarantee | Why include it |
|---|---|---|
| Multi-message IND-CPA public-key encryption | Correct efficient public-key encryption on a meaningful message space, indistinguishable under chosen-plaintext attack for polynomially many encryptions under one public key. State whether the theorem uses a batch or adaptive experiment. | The basic confidential-channel primitive; the first end-to-end target for RSA, factoring and DDH routes. |
| Multi-message IND-CCA2 public-key encryption | Correct efficient public-key encryption with adaptive decryption access, excluding all challenge ciphertexts in a multi-challenge formulation. | The robust encryption endpoint when the adversary can submit ciphertexts for decryption. |

**User ruling:** adopt these two endpoints, with IND-CCA1 documented as an intermediate.
Always write CCA1 or CCA2 explicitly;
“CCA” alone does not choose a game. CCA1 permits decryption queries only before the challenge;
CCA2 permits them afterwards subject to the challenge restriction. The taxonomy is reviewed
in [Pass, Cornell CS 6830, lecture 13 (2009), §1](https://www.cs.cornell.edu/courses/cs6830/2009fa/scribes/lecture13.pdf).

Do not add separate first-class entries for single-bit encryption, single-message security,
the bitwise construction, every weaker notion, or each padding stage. These are supporting
APIs. Non-malleability variants and stronger public-key functionalities can be considered
later when they provide a distinct endpoint required by a construction, rather than an
extra name for an already indexed guarantee.

No multi-message IND-CCA2 public-key construction is currently established in the surveyed
campaign source. Gate 06's encrypt-then-tag CCA2 construction is **private-key encryption**.
A public-key CCA2 row is a future target requiring its own construction/bridge work; no new
external audit or fill is prepared here.

## Shape of a catalog theorem

Each theorem has the form `(assumption A) → (assumption B) → … → ∃ S, targetSecurity S`, with
correctness and algorithmic efficiency bundled or explicitly conjoined. Use named concrete
hardness assumptions when available, keep all remaining premises visible, and show that S
has a meaningful message space. For the fixed-length model, a constraint such as
`S.msgLen = PolyExpr.var` prevents a vacuous empty-message-only witness. The exact final
Lean header and multi-message predicate still require design and checking.

Several assumption sets can lead to the same endpoint; those are useful separate theorems.
A chain of intermediate predicates for the same route is not a separate set of catalog
entries. RSA plus its retained infrastructure, factoring plus its retained infrastructure,
and DDH plus its retained infrastructure are the candidate rows below. Generic hard-core-TDP
facts remain available as the composition API behind these entries.

## Existing APIs and their exact security models

| Existing predicate | Meaning and source | Role here |
|---|---|---|
| `BitPublicKeyScheme.SingleBitSecure` | Indistinguishability of encryptions of bits; `Asymptotic/PublicKey.lean:250`. | Intermediate. |
| `PublicKeyScheme.Secure` | Indistinguishability for every equal-length pair of messages, public key included; `Asymptotic/PublicKey.lean:142`. | Input to the existing many-message lifting. |
| `PublicKeyScheme.MultiMessageSecure` | Polynomially many-message experiment; `Asymptotic/PublicKey.lean:166`. | Existing generic endpoint; do not silently equate this batch predicate with an adaptive oracle game. |
| `Composability.FixedLengthPKScheme.INDSecure .cpa` | Gate 06's two-stage, key-visible CPA oracle game; `Composability/PublicKey.lean` on integration only. | Precise CPA bridge, currently admitted. |
| `Candidates.GroupPKScheme.Secure` | ElGamal's key-dependent group-message selector model; `Candidates/ElGamal.lean:458`. | Separate current model; retain admissible-message correctness and prove the required conversion. |

## Existing generic chain — supporting material, not new catalog tiers

The hard-core-TDP → single-bit → bitwise → multi-message chain is already proved by existing
components. For T : TrapdoorCollection, one-wayness hT and ordinary hard-core security hHC,
the complete composition has the short source-level term:

```lean
  obtain ⟨E⟩ := hHC.nonempty_predEvaluator
  exact ⟨(T.tdpBitScheme E).bitwise,
    (T.tdpBitScheme_singleBitSecure E hT hHC).bitwise.multiMessageSecure⟩
```

This snippet has not been elaborated as a new wrapper. Reuse/index the existing APIs instead
of adding four theorem tiers. Sources: `Asymptotic/PublicKey.lean:749`, `:911`, `:353`,
`:471`, `:529`; [PS10, Algorithm 104.3, Theorem 104.4 and p. 103].
The public-key single-to-many-message hybrid argument also appears in
[Pass, Cornell CS 6830, lecture 13 (2009), Theorem 2](https://www.cs.cornell.edu/courses/cs6830/2009fa/scribes/lecture13.pdf).
This CPA-style bitwise construction must not be reused as a CCA2 length-extension argument.

`OneWay.exists_glPad_singleBitSecure` supplies the hard-core step for fixed-width encodings,
retaining m : PolyExpr and the exact premise

```lean
henc : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)),
  (T.encD (T.index n r) x).length = m.eval n
```

Sources: `Asymptotic/HardCoreCollection.lean:92`, `:489`, `:498` and
`Asymptotic/PublicKey.lean:1059`; [PS10, Theorems 87.3 and 104.4]. This is a useful generic
API on its actual domain, not an RSA instantiation.

## Exact CPA bridge: statement-gated, proof still missing

`BitPublicKeyScheme.exists_padBound` supplies L, its ciphertext padding bound and
`1 ≤ L.eval n`; then `hS.padded_cpa L hL hmsg` supplies the CPA claim for
`S.padded L hL hmsg`. `TrapdoorCollection.tdpBitScheme_padded_cpa` already composes this
route. These remain supporting APIs; the catalog theorem should start from its assumption
set and end at the chosen primitive.

`BitPublicKeyScheme.SingleBitSecure.padded_cpa` is an admission on the integration branch.
Gate06C is now closed at the frozen statement source; its admitted bridge still needs a fill before any claim of a completed exact CPA implication. The
many-message endpoint still needs its precise game and a checked lifting in that model.

## Concrete assumptions: index their actual current endpoints

| Assumption | Existing endpoint | Extra premises | Missing work before a generic CPA-PKE existence theorem |
|---|---|---|---|
| `RSAAssumption` | `(rsaTrapdoor H).OneWay`, via `rsaCollection_oneWay` and `rsaTrapdoor_oneWay` (`Candidates/RSA.lean:2206`, `:2221`) | `H : ArithmeticFP` (`Candidates/Arithmetic.lean:314`) | Goldreich–Levin padding needs a genuine length bridge; exact CPA then needs the Gate 06C bridge. |
| `FactoringAssumption` | `(rabinBlumTrapdoor H).OneWay` (`Candidates/Rabin.lean:3392`) | `ArithmeticFP`, `BlumDensity` remains a hypothesis | Same encoding-length issue and CPA bridge. The plain factoring collection is not itself a trapdoor-permutation conclusion. |
| `DDHAssumption (egGroupGen H G)` | `(elGamal H G).Secure` in `GroupPKScheme` (`Candidates/ElGamal.lean:2211`) | `ArithmeticFP`, `G : SafePrimeGen`, negligible full-length-exception bound `hbig` | Preserve the group-message security/correctness model; a conversion to another PKE record/security game is separate work. |

RSA's construction is `Candidates/RSA.lean:1493`; its concrete RSA root-extraction assumption
is `:105`/`:118`. The generic padding documentation explicitly states the cost:
`Asymptotic/HardCoreCollection.lean:85–91`. Generated RSA elements have width `2*max(n,2)`,
Rabin's width is `2*max(n,3)`; no current candidate satisfies the exact `PolyExpr` equality as
parameterized. The documented per-index-width/bounded-length version is not formalized.

A smaller proposed normalization route is now in `normalization-design.md`: run RSA at n+2
and Blum Rabin at n+3, so their widths become exact polynomials. Existing machine-level
parameter-change APIs and the existing `Negligible.comp_of_le` closure theorem are available.
Collection construction, one-wayness transport and candidate-home width readers remain missing;
the general negligibility theorem needs relocation to Foundations for the lower-layer use.
This is a source-level design, not a completed bridge or a new catalog tier.

**Do not declare a candidate-level theorem by adding that impossible premise.** A future
normalization or generalized padding construction must have a real public contract and proof.
Its statement/fill work is separate from the short Implications wrappers.

## Review and implementation checks

- Every final theorem has an explicit mathematical header, an accurate source docstring and
  all retained hypotheses. Use source-level proof terms through public APIs only.
- Show each witness's actual scheme and security model. Keep the paired correctness theorem
  when the source record does not contain it (GroupPKScheme).
- Check axiom dependencies of the entire composition. Distinguish existing admissions from
  proof completion, even if the new wrapper has no local sorry.
- Use an isolated PR worktree, precise imports, topic facade/root exports and serial module
  checks. No new host is needed for the generic pilot.

**Not yet clear to merge — proposed contents, no new Lean wrapper module checked yet.**

## ===== briefs/pass-shelat-ch5-8/maintainer/rsa-screen-2026-11-11/README.md =====

# RSA / Rabin catalog screen (2026-11-11)

Campaign head `3f921e63d` (after #291). A probe (`Compose.lean`, log `compose.log`) composes only
published theorems; it compiles (rc 0) and both witnesses print `[propext, Classical.choice, Quot.sound]`.

**RSA** (`ArithmeticFP`, `RSAAssumption`):
`rsaTrapdoor_oneWay` → `TrapdoorCollection.shiftParameter_oneWay _ 2` → `TrapdoorCollection.OneWay.exists_glPad_singleBitSecure`
with `m = 2(n+2)` and `henc := rsaTrapdoor_shiftParameter_encD_length` (from #284) → `SingleBitSecure.exists_adaptive_cpa`
(#287, #290, #291) ⇒ `∃ S : FixedLengthPKScheme, S.msgLen = .var ∧ S.AdaptiveINDSecure .cpa`.

**Rabin** (`ArithmeticFP`, `BlumDensity`, `FactoringAssumption`): the same route at `n+3` with
`rabinBlumTrapdoor_oneWay` and `rabinBlumTrapdoor_shiftParameter_encD_length`.

No new proof obligations remain: the catalog entries are short compositions. The witness record
`FixedLengthPKScheme` carries uniform efficient key generation and encryption, polynomial-time
decryption, fixed ciphertext width and perfect correctness. The probe needs the import of
`Encryption.PublicKey.Trapdoor` in addition to `BitwiseCPA`, `Candidates.RSA`, `Candidates.Rabin`.

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
import TCSlib.Complexity.Randomized
import TCSlib.Complexity.TimeHierarchy
import TCSlib.Complexity.SpaceComplexity

import TCSlib.ComputationalModels

import TCSlib.Cryptography.SchnorrProtocol
import TCSlib.Cryptography.SecretSharing
import TCSlib.Cryptography.MPC
import TCSlib.Cryptography.Foundations
import TCSlib.Cryptography.OneWayFunctions
import TCSlib.Cryptography.HardcoreBit
import TCSlib.Cryptography.Pseudorandom
import TCSlib.Cryptography.Asymptotic
import TCSlib.Cryptography.Candidates
import TCSlib.Cryptography.NumberTheory
import TCSlib.Cryptography.Encoding
import TCSlib.Cryptography.LWE
import TCSlib.Cryptography.SIS
import TCSlib.Cryptography.Encryption
import TCSlib.Cryptography.TrapdoorFunctions
import TCSlib.Cryptography.ZeroKnowledge
import TCSlib.Cryptography.Games
import TCSlib.Cryptography.Games.Bridges
import TCSlib.Cryptography.Authentication
import TCSlib.Cryptography.Hashing
import TCSlib.Cryptography.SecureComputation
import TCSlib.Cryptography.Composability
import TCSlib.Cryptography.Encryption.PrivateKey
import TCSlib.Cryptography.Encryption.PublicKey
import TCSlib.Cryptography.Randomness
import TCSlib.Cryptography.Implications

import TCSlib.InformationTheory

import TCSlib.GraphTheory.Kruskal

import TCSlib.KikuchiLDC.Main

import TCSlib.LearningTheory.MistakeBounds
import TCSlib.LearningTheory.Hedge
import TCSlib.LearningTheory.JohnsonLindenstrauss
import TCSlib.LearningTheory.Minimax
import TCSlib.LearningTheory.PAC

## ===== TCSlib/Cryptography/Implications.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Implications.PublicKey

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Implications

The catalog of end-to-end results: an explicit set of hardness assumptions implies the existence of
a fundamental primitive with a precise security notion. Each entry states its full assumption set
and is proved by a short composition of published results; definitions, candidates and reductions
never import this layer.

## Contents

* `PublicKey`: adaptive multi-message IND-CPA public-key encryption with `n`-bit messages, from RSA
  and from factoring.
-/

## ===== TCSlib/Cryptography/Implications/PublicKey.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA
import TCSlib.Cryptography.Encryption.PublicKey.Trapdoor
import TCSlib.Cryptography.Candidates.RSA
import TCSlib.Cryptography.Candidates.Rabin

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Implications: public-key encryption

Catalog of end-to-end results of the form "these hardness assumptions give a public-key encryption
scheme with this security". Each entry states its full assumption set and proves the conclusion by a
short composition of published results. The endpoint here is **adaptive multi-message IND-CPA with
`n`-bit messages**:

`∃ S : FixedLengthPKScheme, S.msgLen = .var ∧ S.AdaptiveINDSecure .cpa`.

`FixedLengthPKScheme` packages uniform polynomial-time key generation and encryption,
polynomial-time decryption, fixed-length ciphertexts and perfect correctness. `msgLen = .var`
makes the message space `{0,1}^n`, so the existential cannot be met by an empty-message scheme.
`AdaptiveINDSecure .cpa` is the left-or-right game of [PS10, Definition 171.5] with one public
key, one hidden bit and a polynomial number of adaptively chosen challenges.

## Main results

* `Implications.PublicKey.exists_adaptiveCPA_of_rsa`: from `ArithmeticFP` and `RSAAssumption`.
* `Implications.PublicKey.exists_adaptiveCPA_of_factoring`: from `ArithmeticFP`, `BlumDensity` and
  `FactoringAssumption`.

## The route

Both entries take the same steps:
1. A one-way trapdoor permutation collection (`rsaTrapdoor_oneWay`, `rabinBlumTrapdoor_oneWay`).
2. It is run at parameter `n + 2` (RSA) or `n + 3` (Rabin)
   (`TrapdoorCollection.shiftParameter_oneWay`), so that its encoding width is exactly the
   polynomial `2(n + 2)` or `2(n + 3)`
   (`rsaTrapdoor_shiftParameter_encD_length`, `rabinBlumTrapdoor_shiftParameter_encD_length`).
3. The Goldreich–Levin padded collection then gives a secure single-bit scheme of Algorithm 104.3
   (`TrapdoorCollection.OneWay.exists_glPad_singleBitSecure`) [PS10, Theorems 87.3 and 104.4].
4. The padded bitwise scheme of p. 103 is adaptively CPA-secure
   (`BitPublicKeyScheme.SingleBitSecure.exists_adaptive_cpa`, from `bitwise_padded_cpa` and
   `FixedLengthPKScheme.INDSecure.adaptive_cpa`).

The arithmetic efficiency premise `ArithmeticFP` and Rabin's prime-density premise `BlumDensity`
stay explicit hypotheses.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010:
  Theorems 53.2 and 57.2 (RSA), §2.12 and Theorems 61.8 and 63.10 (Rabin–Blum), Theorem 87.3
  (Goldreich–Levin),
  Algorithm 104.3 and Theorem 104.4, p. 103 (the bitwise scheme), Definition 171.5.
-/

namespace TCSlib.Cryptography.Implications.PublicKey

open TCSlib.Cryptography TCSlib.Cryptography.Composability TCSlib.Cryptography.Candidates Complexity

/-- **RSA gives adaptively CPA-secure public-key encryption with `n`-bit messages.** Under the RSA
assumption and arithmetic efficiency, some fixed-length public-key scheme with message length
`PolyExpr.var` is secure in the adaptive multi-challenge CPA game:
`ArithmeticFP → RSAAssumption →
∃ S : FixedLengthPKScheme, S.msgLen = .var ∧ S.AdaptiveINDSecure .cpa`
[PS10, Theorems 53.2 and 57.2, Theorems 87.3 and 104.4, p. 103, Definition 171.5].

**Proof sketch.** `rsaTrapdoor_oneWay` and the shift by `2`
(`TrapdoorCollection.shiftParameter_oneWay`) give a one-way trapdoor collection whose encodings have
width exactly `2(n + 2)` (`rsaTrapdoor_shiftParameter_encD_length`). Goldreich–Levin padding gives a
secure single-bit scheme (`TrapdoorCollection.OneWay.exists_glPad_singleBitSecure`), and
`BitPublicKeyScheme.SingleBitSecure.exists_adaptive_cpa` finishes. -/
theorem exists_adaptiveCPA_of_rsa (H : ArithmeticFP) (hR : RSAAssumption) :
    ∃ S : FixedLengthPKScheme, S.msgLen = .var ∧ S.AdaptiveINDSecure .cpa := by
  have hT := (rsaTrapdoor H).shiftParameter_oneWay 2 (rsaTrapdoor_oneWay H hR)
  obtain ⟨_, hE⟩ := TrapdoorCollection.OneWay.exists_glPad_singleBitSecure _
    (rsaTrapdoor_shiftParameter_encD_length H) hT
  obtain ⟨S, hmsg, -, hS⟩ := hE.exists_adaptive_cpa
  exact ⟨S, hmsg, hS⟩

/-- **Factoring gives adaptively CPA-secure public-key encryption with `n`-bit messages.** Under the
factoring assumption, the density of Blum primes and arithmetic efficiency, some fixed-length
public-key scheme with message length `PolyExpr.var` is secure in the adaptive multi-challenge CPA
game: `ArithmeticFP → BlumDensity → FactoringAssumption →
∃ S : FixedLengthPKScheme, S.msgLen = .var ∧ S.AdaptiveINDSecure .cpa`
[PS10, §2.12, Theorems 61.8 and 63.10, Theorems 87.3 and 104.4, p. 103, Definition 171.5].

**Proof sketch.** As `exists_adaptiveCPA_of_rsa`, with the Rabin–Blum trapdoor collection
(`rabinBlumTrapdoor_oneWay`) shifted by `3`, whose encodings have width exactly `2(n + 3)`
(`rabinBlumTrapdoor_shiftParameter_encD_length`). -/
theorem exists_adaptiveCPA_of_factoring (H : ArithmeticFP) (hD : BlumDensity)
    (hF : FactoringAssumption) :
    ∃ S : FixedLengthPKScheme, S.msgLen = .var ∧ S.AdaptiveINDSecure .cpa := by
  have hT := (rabinBlumTrapdoor H).shiftParameter_oneWay 3 (rabinBlumTrapdoor_oneWay H hD hF)
  obtain ⟨_, hE⟩ := TrapdoorCollection.OneWay.exists_glPad_singleBitSecure _
    (rabinBlumTrapdoor_shiftParameter_encD_length H) hT
  obtain ⟨S, hmsg, -, hS⟩ := hE.exists_adaptive_cpa
  exact ⟨S, hmsg, hS⟩

end TCSlib.Cryptography.Implications.PublicKey

## ===== TCSlib/Cryptography/Asymptotic/CollectionShift.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Asymptotic.Collections
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Constant shifts of trapdoor collections

Replace the security parameter `n` by `n+c` in all three uniform machines of
a trapdoor permutation collection [PS10, Definition 56.1]. This lets collections with a small-parameter
fallback schedule supply exact polynomial encoding widths.

## Main definitions

* `TrapdoorCollection.shiftParameter` shifts the generator, sampler and inverter together.
* `TrapdoorCollection.shiftGenCoins`, `shiftSampleCoins` and `shiftInvCoins` match their tapes.

## Main results

* `TrapdoorCollection.shiftParameter_encD_length` transports exact encoding widths.
* `TrapdoorCollection.shiftParameter_sampleClose` transports sampler closeness.
* `TrapdoorCollection.shiftParameter_oneWay` transports one-wayness.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
-/

namespace TCSlib.Cryptography.TrapdoorCollection

open Complexity Turing

/-- A uniformity-preserving parameter change and its coin and activation laws. -/
private structure ShiftedMachine (A : NUPPT) (c : ℕ) where
  machine : NUPPT
  uniform : A.Uniform → machine.Uniform
  coins : ∀ n, machine.Coins n ≃ A.Coins (n + c)
  coins_ofFn : ∀ n (r : machine.Coins n), List.ofFn (coins n r) = List.ofFn r
  runAt_eq : ∀ n y (r : machine.Coins n), machine.runAt n y r = A.runAt (n + c) y (coins n r)

/-- The polynomial parameter-change machine has the required tape and activation laws.

**Proof sketch.** Instantiate the existing machine with the additive polynomial.
Transport the tapes using the coin-length equality and preserve their raw encodings. -/
private theorem shiftedMachine_exists (A : NUPPT) (c : ℕ) : Nonempty (ShiftedMachine A c) := by
  obtain ⟨B, hBc, hBu, hBr⟩ := A.exists_reparam (.add .var (.const c))
  have hlen (n : ℕ) : B.coinLen n = A.coinLen (n + c) := by
    simp only [NUPPT.coinLen_eq, hBc, PolyExpr.eval_subst, PolyExpr.eval_add, PolyExpr.eval_var,
      PolyExpr.eval_const]
  let e (n : ℕ) : B.Coins n ≃ A.Coins (n + c) :=
    Equiv.arrowCongr (finCongr (hlen n)) (Equiv.refl Bool)
  have he (n : ℕ) (r : B.Coins n) : List.ofFn (e n r) = List.ofFn r :=
    (List.ofFn_congr (hlen n) r).symm
  refine ⟨⟨B, hBu, e, he, fun n y r => ?_⟩⟩
  simp only [NUPPT.runAt_eq, he, hBr, PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]

/-- Choose the certified machine for this constant shift. -/
private noncomputable def shiftedMachine (A : NUPPT) (c : ℕ) : ShiftedMachine A c :=
  Classical.choice (shiftedMachine_exists A c)

/-- Shift the security parameter of the generator, sampler, and inverter from n to n+c.
Keep the domains, encoded permutation, evaluator, and decoder of [PS10, Definition 56.1].

**Proof sketch.** Apply the same polynomial parameter change to the three machines.
Use their activation laws to transfer sampler membership and trapdoor inversion on
each generator tape. -/
noncomputable def shiftParameter (T : TrapdoorCollection) (c : ℕ) : TrapdoorCollection :=
  { T with
    gen := (shiftedMachine T.gen c).machine
    gen_uniform := (shiftedMachine T.gen c).uniform T.gen_uniform
    sample := (shiftedMachine T.sample c).machine
    sample_uniform := (shiftedMachine T.sample c).uniform T.sample_uniform
    sample_spec := by
      intro n r s
      rw [(shiftedMachine T.gen c).runAt_eq, (shiftedMachine T.sample c).runAt_eq]
      exact T.sample_spec (n + c) ((shiftedMachine T.gen c).coins n r)
        ((shiftedMachine T.sample c).coins n s)
    inv := (shiftedMachine T.inv c).machine
    inv_uniform := (shiftedMachine T.inv c).uniform T.inv_uniform
    inv_spec := by
      intro n r
      rw [(shiftedMachine T.gen c).runAt_eq]
      intro y s
      rw [(shiftedMachine T.inv c).runAt_eq]
      exact T.inv_spec (n + c) ((shiftedMachine T.gen c).coins n r) y
        ((shiftedMachine T.inv c).coins n s) }

/-- The shifted and original generator tapes have the same length at corresponding parameters. -/
noncomputable def shiftGenCoins (T : TrapdoorCollection) (c n : ℕ) :
    (T.shiftParameter c).gen.Coins n ≃ T.gen.Coins (n + c) :=
  (shiftedMachine T.gen c).coins n

/-- The generator coin transport preserves the encoded tape. -/
theorem shiftGenCoins_ofFn (T : TrapdoorCollection) (c n : ℕ) (r : (T.shiftParameter c).gen.Coins n) :
    List.ofFn (T.shiftGenCoins c n r) = List.ofFn r :=
  (shiftedMachine T.gen c).coins_ofFn n r

/-- The shifted and original sampler tapes have the same length at corresponding parameters. -/
noncomputable def shiftSampleCoins (T : TrapdoorCollection) (c n : ℕ) :
    (T.shiftParameter c).sample.Coins n ≃ T.sample.Coins (n + c) :=
  (shiftedMachine T.sample c).coins n

/-- The sampler coin transport preserves the encoded tape. -/
theorem shiftSampleCoins_ofFn (T : TrapdoorCollection) (c n : ℕ)
    (r : (T.shiftParameter c).sample.Coins n) :
    List.ofFn (T.shiftSampleCoins c n r) = List.ofFn r :=
  (shiftedMachine T.sample c).coins_ofFn n r

/-- The shifted and original inverter tapes have the same length at corresponding parameters. -/
noncomputable def shiftInvCoins (T : TrapdoorCollection) (c n : ℕ) :
    (T.shiftParameter c).inv.Coins n ≃ T.inv.Coins (n + c) :=
  (shiftedMachine T.inv c).coins n

/-- The inverter coin transport preserves the encoded tape. -/
theorem shiftInvCoins_ofFn (T : TrapdoorCollection) (c n : ℕ) (r : (T.shiftParameter c).inv.Coins n) :
    List.ofFn (T.shiftInvCoins c n r) = List.ofFn r :=
  (shiftedMachine T.inv c).coins_ofFn n r

/-- The shifted generator at n returns the original output at n+c. -/
theorem shiftParameter_gen_runAt (T : TrapdoorCollection) (c n : ℕ) (y : List Bool)
    (r : (T.shiftParameter c).gen.Coins n) :
    (T.shiftParameter c).gen.runAt n y r = T.gen.runAt (n + c) y (T.shiftGenCoins c n r) :=
  (shiftedMachine T.gen c).runAt_eq n y r

/-- The shifted sampler at n returns the original output at n+c. -/
theorem shiftParameter_sample_runAt (T : TrapdoorCollection) (c n : ℕ) (y : List Bool)
    (r : (T.shiftParameter c).sample.Coins n) :
    (T.shiftParameter c).sample.runAt n y r = T.sample.runAt (n + c) y (T.shiftSampleCoins c n r) :=
  (shiftedMachine T.sample c).runAt_eq n y r

/-- The shifted inverter at n returns the original output at n+c. -/
theorem shiftParameter_inv_runAt (T : TrapdoorCollection) (c n : ℕ) (y : List Bool)
    (r : (T.shiftParameter c).inv.Coins n) :
    (T.shiftParameter c).inv.runAt n y r = T.inv.runAt (n + c) y (T.shiftInvCoins c n r) :=
  (shiftedMachine T.inv c).runAt_eq n y r

/-- The shifted generator returns the same index at n as the original at n+c. -/
theorem shiftParameter_index (T : TrapdoorCollection) (c n : ℕ) (r : (T.shiftParameter c).gen.Coins n) :
    (T.shiftParameter c).index n r = T.index (n + c) (T.shiftGenCoins c n r) := by
  rw [Collection.index_eq, Collection.index_eq, T.shiftParameter_gen_runAt]

/-- The shifted generator returns the same trapdoor at n as the original at n+c. -/
theorem shiftParameter_trap (T : TrapdoorCollection) (c n : ℕ) (r : (T.shiftParameter c).gen.Coins n) :
    (T.shiftParameter c).trap n r = T.trap (n + c) (T.shiftGenCoins c n r) := by
  rw [Collection.trap_eq, Collection.trap_eq, T.shiftParameter_gen_runAt]

/-- The domains of the shifted collection agree with the original domains at every index. -/
def shiftParameter_domEquiv (T : TrapdoorCollection) (c : ℕ) (i : List Bool) :
    (T.shiftParameter c).D i ≃ T.D i := Equiv.refl _

/-- The domain equivalence acts as the identity. -/
theorem shiftParameter_domEquiv_apply (T : TrapdoorCollection) (c : ℕ) (i : List Bool)
    (x : (T.shiftParameter c).D i) : T.shiftParameter_domEquiv c i x = x := rfl

/-- The shifted encoder reads through the original domain. -/
theorem shiftParameter_encD (T : TrapdoorCollection) (c : ℕ) (i : List Bool)
    (x : (T.shiftParameter c).D i) :
    (T.shiftParameter c).encD i x = T.encD i (T.shiftParameter_domEquiv c i x) := rfl

/-- The shifted decoder is the original decoder carried back through the domain equivalence. -/
theorem shiftParameter_decD (T : TrapdoorCollection) (c : ℕ) (i w : List Bool) :
    (T.shiftParameter c).decD i w = (T.decD i w).map (T.shiftParameter_domEquiv c i).symm := by
  show T.decD i w = _
  cases T.decD i w <;> rfl

/-- The shifted permutation reads through the original domain. -/
theorem shiftParameter_perm (T : TrapdoorCollection) (c : ℕ) (i : List Bool)
    (x : (T.shiftParameter c).D i) :
    (T.shiftParameter c).perm i x =
      (T.shiftParameter_domEquiv c i).symm (T.perm i (T.shiftParameter_domEquiv c i x)) := rfl

/-- The shifted evaluator equals the original evaluator. -/
theorem shiftParameter_eval (T : TrapdoorCollection) (c : ℕ) :
    (T.shiftParameter c).eval = T.eval := rfl

/-- The shifted function reads through the original domain. -/
theorem shiftParameter_f (T : TrapdoorCollection) (c : ℕ) (i : List Bool)
    (x : (T.shiftParameter c).D i) :
    (T.shiftParameter c).f i x = T.f i (T.shiftParameter_domEquiv c i x) := rfl

/-- Exact encoding widths transfer to the shifted parameter for every generator tape.

**Proof sketch.** Generalize over the domain element and rewrite the generated index
using the generator coin equivalence. The shifted encoding is the original one. -/
theorem shiftParameter_encD_length (T : TrapdoorCollection) (c : ℕ) (W : ℕ → ℕ)
    (h : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = W n)
    (n : ℕ) (r : (T.shiftParameter c).gen.Coins n)
    (x : (T.shiftParameter c).D ((T.shiftParameter c).index n r)) :
    ((T.shiftParameter c).encD ((T.shiftParameter c).index n r) x).length = W (n + c) := by
  revert x
  change ∀ x : T.D ((T.shiftParameter c).index n r), (T.encD _ x).length = W (n + c)
  rw [T.shiftParameter_index]
  exact h (n + c) (T.shiftGenCoins c n r)

/-- Statistical closeness at n+c transfers to the shifted sampler at n.

**Proof sketch.** Match each generator tape with its original tape. Relabel the uniform
sampler tape along the coin equivalence, using the sampler's activation law. -/
theorem shiftParameter_sampleClose (T : TrapdoorCollection) (c : ℕ) (δ : ℕ → ℝ)
    (h : T.toCollection.SampleClose δ) :
    (T.shiftParameter c).toCollection.SampleClose (fun n => δ (n + c)) := by
  rw [Collection.sampleClose_iff] at h ⊢
  intro n r
  change StatClose
    (fun s : (T.shiftParameter c).sample.Coins n =>
      T.decD ((T.shiftParameter c).index n r)
        ((T.shiftParameter c).sample.runAt n ((T.shiftParameter c).index n r) s))
    (fun x : T.D ((T.shiftParameter c).index n r) => some x) (δ (n + c))
  rw [T.shiftParameter_index]
  simp only [T.shiftParameter_sample_runAt]
  exact (h (n + c) (T.shiftGenCoins c n r)).comp_equiv_left (T.shiftSampleCoins c n)

/-- Each adversary for the shifted collection has an original-parameter adversary with
the same inversion probability at m=n+c.

**Proof sketch.** Run A at m-c with the first A.coinLen(m-c) bits. Relabel the
generator tape and split the longer adversary tape into the consumed prefix and an
independent suffix. Averaging over the unread suffix leaves the event probability
unchanged. -/
theorem shiftParameter_exists_invProbAt (T : TrapdoorCollection) (c : ℕ) (A : NUPPT) :
    ∃ B : NUPPT, ∀ n,
      (T.shiftParameter c).toCollection.invProbAt A n = T.toCollection.invProbAt B (n + c) := by
  obtain ⟨B, hBc, hB⟩ := A.exists_reparam_advice (fun m => m - c) .var
    (fun m => by rw [PolyExpr.eval_var]; exact Nat.sub_le m c)
  refine ⟨B, fun n => ?_⟩
  have hlen : B.coinLen (n + c) =
      A.coinLen n + (A.coinLen (n + c) - A.coinLen n) := by
    have hle : A.coinLen n ≤ A.coinLen (n + c) := by
      simp only [NUPPT.coinLen_eq]
      exact A.coins.eval_mono (Nat.le_add_right n c)
    simp only [NUPPT.coinLen_eq, hBc, PolyExpr.eval_subst, PolyExpr.eval_var] at hle ⊢
    omega
  let e := EnsembleLemmas.coinsEquiv hlen
  simp only [Collection.invProbAt_eq]
  rw [← HardcoreBit.uexp_comp_equiv (T.shiftGenCoins c n)]
  congr 1
  funext r
  let i := (T.shiftParameter c).index n r
  change uprob (fun z : T.D i × A.Coins n =>
    ∃ x', T.decD i (A.runAt n (pairEncode i (T.f i z.1)) z.2) = some x' ∧
      T.f i x' = T.f i z.1) = _
  have hi : i = T.index (n + c) (T.shiftGenCoins c n r) := T.shiftParameter_index c n r
  rw [hi]
  rw [uprob_prod, uprob_prod]
  congr 1
  funext x
  rw [← uprob_comp_equiv e]
  simp only [NUPPT.runAt_eq, hB, Nat.add_sub_cancel, e, EnsembleLemmas.take_ofFn_coinsEquiv]
  exact (uprob_fst _).symm

/-- Constant right shifts preserve one-wayness for trapdoor permutation collections
This is a parameter-change consequence of [PS10, Definitions 41.1 and 56.1].

**Proof sketch.** Shift the sampler error by the same offset. Apply the inversion
probability equality to each adversary, then use negligibility along n ↦ n+c in both
cases. -/
theorem shiftParameter_oneWay (T : TrapdoorCollection) (c : ℕ) (h : T.OneWay) :
    (T.shiftParameter c).OneWay := by
  rw [TrapdoorCollection.oneWay_iff] at h ⊢
  obtain ⟨δ, hδ, hclose⟩ := h.sampleClose
  refine ⟨⟨_, hδ.comp_of_le (fun n => n + c) (fun n => Nat.le_add_right n c),
    T.shiftParameter_sampleClose c δ hclose⟩, fun A => ?_⟩
  obtain ⟨B, hB⟩ := T.shiftParameter_exists_invProbAt c A
  have hshift := (h.hard B).comp_of_le (fun n => n + c) (fun n => Nat.le_add_right n c)
  exact (funext hB) ▸ hshift

end TCSlib.Cryptography.TrapdoorCollection

## ===== TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA
import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA.Eager
import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA.Planted
import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA.QueryHandler

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The bitwise scheme under chosen-plaintext attack

The bitwise scheme of [PS10, p. 103] encrypts an `n`-bit message one bit at a time with a
single-bit scheme (such as the trapdoor scheme of Algorithm 104.3, secure by Theorem 104.4).
Padded to fixed-length ciphertexts (`PublicKeyScheme.padded`), it is a fixed-length scheme with
`n`-bit messages. If the single-bit scheme is secure, the padded bitwise scheme is CPA-secure in
the game of [PS10, Definition 171.5], where the adversary chooses its two messages after seeing
the public key, and hence secure in the adaptive multi-challenge game.

Ensemble security of the bitwise scheme for message pairs fixed in advance
(`BitPublicKeyScheme.SingleBitSecure.bitwise`) is not enough here: there the messages cannot
depend on the public key. The proof below therefore goes back to single-bit security.

## Main results

* `BitPublicKeyScheme.SingleBitSecure.bitwise_padded_cpa`: the padded bitwise scheme is
  CPA-secure.
* `BitPublicKeyScheme.SingleBitSecure.bitwise_padded_adaptive_cpa`: and adaptively CPA-secure.
* `BitPublicKeyScheme.SingleBitSecure.exists_adaptive_cpa`: a fixed-length scheme with `n`-bit
  messages and the same key generator is adaptively CPA-secure.

## Contents

* `BitwiseCPA/Eager`: eager challenge coins under CPA, resampling one coordinate of a uniform
  tuple, and readers of the padded encryptor.
* `BitwiseCPA/Planted`: the planted bitwise challenge answer and the reduction's final bit.
* `BitwiseCPA/QueryHandler`: the query-recording handler with advice and its machine by T1.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  p. 103 (the bitwise scheme and the hybrid argument); Algorithm 104.3 and Theorem 104.4 (the
  single-bit trapdoor scheme, book pp. 104–105); Definition 171.5 (book p. 171).
-/

namespace TCSlib.Cryptography.Composability

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! ### The hybrid argument -/

section BitwiseCPAProof

open ChallengeSim BitwiseSim ProbComp

/-- The tuple of hybrid `j` on the challenge `l = m₀ ‖ m₁`: block `i` encrypts, with the coins
`v_i`, bit `i` of the right message (`l_{n+i}`) if `i < j` and of the left message (`l_i`)
otherwise. -/
private def hybCt (S : BitPublicKeyScheme) (n j : ℕ) (pk : List Bool)
    (v : Fin n → S.enc.Coins n) (l : List Bool) : List Bool :=
  PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n =>
    S.enc.runAt n (pairEncode pk [if (i : ℕ) < j then l.getD (n + i) false else l.getD i false])
      (v i))

/-- **The hybrid `H_j`** (step 1): sample the keys, `A`'s coins and `n` single-bit encryption
tapes `v`, run `A` against the CPA oracles whose first challenge `⟨m₀, m₁⟩` is answered with the
padded tuple of hybrid `j` (`hybCt`, later challenges repeat it), and output `A`'s bit. -/
private noncomputable def hybGame (S : BitPublicKeyScheme) (L : PolyExpr)
    (hL : ∀ n (rg : S.bitwise.gen.Coins n) (m : Fin n → Bool) (re : S.bitwise.enc.Coins n),
      2 * (S.bitwise.enc.runAt n (pairEncode (pairFstD (S.bitwise.gen.runAt n [] rg))
        (List.ofFn m)) re).length + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n) (A : NUPPT) (q n j : ℕ) : ProbComp Bool :=
  (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (A.Coins n)).bind fun r =>
  (ProbComp.sample (Fin n → S.enc.Coins n)).bind fun v =>
  .pure ((chRun (fun mm => padCt (L.eval n)
      (hybCt S n j (pairFstD (S.gen.runAt n [] rg)) v (List.ofFn mm)))
    (A.toCompOn ((S.bitwise.padded L hL hmsg).indCodec n) n q
      (pairFstD (S.gen.runAt n [] rg)) r) none).1 0)

/-- The bitwise encryptor on a coin list: the tuple of the single-bit encryptions with the
consecutive coin segments (`bitwise_enc`, `bitwise_enc_runAtL`). -/
private theorem bitwise_runAtL (S : BitPublicKeyScheme) (n : ℕ) (pk : List Bool)
    (m : Fin n → Bool) (r : List Bool) :
    S.bitwise.enc.runAtL n (pairEncode pk (List.ofFn m)) r =
      PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n =>
        S.enc.runAtL n (pairEncode pk [m i]) (coinBlock (S.enc.coinLen n) i r)) := by
  rw [BitPublicKeyScheme.bitwise_enc]
  exact BitPublicKeyScheme.bitwise_enc_runAtL S n pk m r

/-- The bitwise encryptor on the coin blocks `v`: the tuple of the single-bit encryptions with
coins `v_i` (`bitwiseEncCoins_ofFn`, `coinBlock_ofFn_coinBlocks`). -/
private theorem bitwise_runAt_blocks (S : BitPublicKeyScheme) (n : ℕ) (pk : List Bool)
    (m : Fin n → Bool) (v : Fin n → S.enc.Coins n) :
    S.bitwise.enc.runAt n (pairEncode pk (List.ofFn m)) (S.bitwiseEncCoins n v) =
      PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n =>
        S.enc.runAt n (pairEncode pk [m i]) (v i)) := by
  rw [NUPPT.runAt_eq, bitwise_runAtL, BitPublicKeyScheme.bitwiseEncCoins_ofFn]
  refine congrArg (fun l => PrivateKeyScheme.encodeList (List.ofFn l)) (funext fun i => ?_)
  rw [coinBlock_ofFn_coinBlocks, ← NUPPT.runAt_eq]

/-- The selected half of a challenge query, as the list of its `n` bits read from the query. -/
private theorem ofFn_half {k n : ℕ} (hk : k = n) (b : Bool) (mm : Fin (k + k) → Bool) :
    List.ofFn (if b then (FixedLengthScheme.splitHalf mm).2
      else (FixedLengthScheme.splitHalf mm).1) =
      List.ofFn (fun i : Fin n => (List.ofFn mm).getD ((if b then n else 0) + i) false) := by
  subst hk
  apply List.ext_getElem
  · cases b <;> simp
  · intro t h₁ h₂
    have ht : t < k := by cases b <;> simpa using h₂
    cases b
    · simp [FixedLengthScheme.splitHalf_fst, List.getD_eq_getElem?_getD]
      rw [dif_pos (by omega)]
      rfl
    · simp [FixedLengthScheme.splitHalf_snd, List.getD_eq_getElem?_getD]
      exact congrArg mm (Fin.ext (Nat.add_comm _ _))

/-- A list of `n + n` bits is its first and its last `n` bits. -/
private theorem ofFn_getD_split {n : ℕ} (l : List Bool) (hl : l.length = n + n) :
    l = List.ofFn (fun i : Fin n => l.getD i false) ++
      List.ofFn (fun i : Fin n => l.getD (n + i) false) := by
  apply List.ext_getElem
  · simp [hl]
  · intro t h₁ h₂
    rw [List.getElem_append]
    split
    · next h => simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁]
    · next h =>
      simp only [List.getElem_ofFn, List.length_ofFn] at h ⊢
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      congr 1
      omega

/-- **The ends of the hybrids are the CPA games** (step 1):
`Pr[Ind_b = 1] = Pr[H_{j_b} = 1]` with `j_0 = 0`, `j_1 = n`.

**Proof sketch.** Eager coins (`expect_simulate_indImpl_cpa`); the padded bitwise encryptor pads
the tuple of single-bit encryptions (`padded_enc_runAt`, `bitwise_runAt_blocks`) on the coin
blocks `v` (the bijection `bitwiseEncCoins`, then `coinsCongr`), and bit `i` of the selected
half is `l_{n+i}` for `b = 1` and `l_i` for `b = 0` (`ofFn_half`). -/
private theorem accept_indGame_eq (S : BitPublicKeyScheme) (L : PolyExpr)
    (hL : ∀ n (rg : S.bitwise.gen.Coins n) (m : Fin n → Bool) (re : S.bitwise.enc.Coins n),
      2 * (S.bitwise.enc.runAt n (pairEncode (pairFstD (S.bitwise.gen.runAt n [] rg))
        (List.ofFn m)) re).length + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n) (A : NUPPT) (q n : ℕ) (b : Bool) :
    accept ((S.bitwise.padded L hL hmsg).indGame .cpa A q b n) =
      accept (hybGame S L hL hmsg A q n (if b then n else 0)) := by
  have hgen : (S.bitwise.padded L hL hmsg).gen = S.gen :=
    (PublicKeyScheme.padded_gen _ _ _ _).trans (BitPublicKeyScheme.bitwise_gen S)
  have hk : (S.bitwise.padded L hL hmsg).msgLen.eval n = n := by
    rw [PublicKeyScheme.padded_msgLen, PolyExpr.eval_var]
  rw [accept_eq, accept_eq, FixedLengthPKScheme.indGame_eq, hgen]
  unfold hybGame
  rw [prob_bind, prob_bind]
  refine congrArg _ (funext fun rg => ?_)
  rw [prob_bind, prob_bind]
  refine congrArg _ (funext fun r => ?_)
  rw [prob_bind, prob_bind]
  refine (expect_simulate_indImpl_cpa _ b n _ _
    (fun a : Fin 1 → Bool => ProbComp.prob (.pure (a 0)) (· = true)) _).trans ?_
  rw [← expect_sample_equiv ((S.bitwiseEncCoins n).trans
    (NUPPT.coinsCongr (padded_enc_coins S.bitwise L hL hmsg) n))]
  refine congrArg _ (funext fun v => ?_)
  refine congrArg (fun g => ProbComp.prob (.pure ((chRun g
    (A.toCompOn ((S.bitwise.padded L hL hmsg).indCodec n) n q (pairFstD (S.gen.runAt n [] rg)) r)
      none).1 0)) (· = true)) (funext fun mm => ?_)
  rw [padded_enc_runAt, Equiv.trans_apply, NUPPT.coinsCongr_ofFn,
    ofFn_half hk b (cast ((S.bitwise.padded L hL hmsg).indSpec_challengeDom n) mm),
    AdaptiveCPA.ofFn_cast ((S.bitwise.padded L hL hmsg).inLens_one n), ← NUPPT.runAt_eq,
    bitwise_runAt_blocks]
  unfold hybCt
  refine congrArg (fun l => padCt (L.eval n) (PrivateKeyScheme.encodeList (List.ofFn l)))
    (funext fun i => ?_)
  cases b <;> simp [i.isLt]

/-- **Planting a bit is resampling a coin block**: the tuple whose block `j` is `Enc(β; re)` and
whose other blocks are those of hybrid `j` with coins `v` is the bitwise tuple of the message
with bit `j` replaced by `β`, with coin block `j` replaced by `re`. -/
private theorem planted_eq (S : BitPublicKeyScheme) (n j : ℕ) (hj : j < n) (pk : List Bool)
    (v : Fin n → S.enc.Coins n) (re : S.enc.Coins n) (β : Bool) (l : List Bool) :
    PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n =>
        if (i : ℕ) < j then S.enc.runAt n (pairEncode pk [l.getD (n + i) false]) (v i)
        else if (i : ℕ) = j then S.enc.runAt n (pairEncode pk [β]) re
        else S.enc.runAt n (pairEncode pk [l.getD i false]) (v i)) =
      PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n =>
        S.enc.runAt n (pairEncode pk [if (i : ℕ) < j then l.getD (n + i) false
          else if (i : ℕ) = j then β else l.getD i false]) (Function.update v ⟨j, hj⟩ re i)) := by
  refine congrArg (fun l => PrivateKeyScheme.encodeList (List.ofFn l)) (funext fun i => ?_)
  by_cases h₁ : (i : ℕ) < j
  · have hne : i ≠ ⟨j, hj⟩ := fun h => by rw [h] at h₁; exact lt_irrefl _ h₁
    simp only [h₁, if_true, Function.update_of_ne hne]
  · by_cases h₂ : (i : ℕ) = j
    · have heq : i = ⟨j, hj⟩ := Fin.ext h₂
      subst heq
      simp only [h₁, if_false, if_true, Function.update_self]
    · have hne : i ≠ ⟨j, hj⟩ := fun h => h₂ (by rw [h])
      simp only [h₁, h₂, if_false, Function.update_of_ne hne]

/-- **Hybrids `j` and `j + 1` with coin block `j` resampled** plant `Enc(l_j; re)`
(`t = false`) and `Enc(l_{n+j}; re)` (`t = true`) at block `j` (`planted_eq`). -/
private theorem hybCt_update (S : BitPublicKeyScheme) (n j : ℕ) (hj : j < n) (pk : List Bool)
    (v : Fin n → S.enc.Coins n) (re : S.enc.Coins n) (l : List Bool) (t : Bool) :
    hybCt S n (if t then j + 1 else j) pk (Function.update v ⟨j, hj⟩ re) l =
      PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n =>
        if (i : ℕ) < j then S.enc.runAt n (pairEncode pk [l.getD (n + i) false]) (v i)
        else if (i : ℕ) = j then
          S.enc.runAt n (pairEncode pk [if t then l.getD (n + j) false else l.getD j false]) re
        else S.enc.runAt n (pairEncode pk [l.getD i false]) (v i)) := by
  rw [planted_eq S n j hj]
  unfold hybCt
  refine congrArg (fun l => PrivateKeyScheme.encodeList (List.ofFn l)) (funext fun i => ?_)
  refine congrArg (fun b => S.enc.runAt n (pairEncode pk [b]) (Function.update v ⟨j, hj⟩ re i)) ?_
  rcases lt_trichotomy (i : ℕ) j with h | h | h
  · have h' : (i : ℕ) < j + 1 := by omega
    cases t <;> simp [h, h']
  · cases t <;> simp [h]
  · have h₁ : ¬ (i : ℕ) < j := by omega
    have h₂ : (i : ℕ) ≠ j := by omega
    have h₃ : ¬ (i : ℕ) < j + 1 := by omega
    cases t <;> simp [h₁, h₂, h₃]

/-- The advice length of the reduction's handler: `2n + 2(n + 1)·B(n) + 4`. -/
private def bwLaux (S : BitPublicKeyScheme) : PolyExpr :=
  .add (.add (.mul (.const 2) .var) (.mul (.const 2) (.mul (.add .var (.const 1)) S.enc.coins)))
    (.const 4)

/-- The reduction's advice at `n`: `⟨1^{j⋆(n)}, ⟨1^{(j⋆(n)+1)·B(n)}, 0^…⟩⟩`, padded with zeros to
`bwLaux S` bits. -/
private def bwAux (S : BitPublicKeyScheme) (js : ℕ → ℕ) (n : ℕ) : List Bool :=
  pairEncode (List.replicate (js n) true)
    (pairEncode (List.replicate ((js n + 1) * S.enc.coinLen n) true)
      (List.replicate ((bwLaux S).eval n - (2 * js n + 2 * ((js n + 1) * S.enc.coinLen n) + 4))
        false))

/-- The advice has `bwLaux S` bits when `j⋆(n) ≤ n`. -/
private theorem bwAux_length (S : BitPublicKeyScheme) (js : ℕ → ℕ) (hjs : ∀ n, js n ≤ n)
    (n : ℕ) : (bwAux S js n).length = (bwLaux S).eval n := by
  have h := Nat.mul_le_mul_right (S.enc.coinLen n) (Nat.add_le_add_right (hjs n) 1)
  have h' := hjs n
  simp only [bwAux, bwLaux, length_pairEncode, List.length_replicate, PolyExpr.eval_add,
    PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var, ← NUPPT.coinLen_eq]
  omega

/-- **The exact identity of step 3.** Let `D` be the machine of `exists_qHandlerMachine` for the
handler with advice `bwAux S js` (the index `j = j⋆(n)`), answer `plantAns` and final bit
`plantOut`. At `n` with `j < n`, the advantage between the hybrids `H_j` and `H_{j+1}` equals
`D`'s advantage between `⟨pk, Enc_pk(0)⟩` and `⟨pk, Enc_pk(1)⟩`.

**Proof sketch.** Fix `n`, the keys and `A`'s coins. Both hybrids answer `A`'s first challenge
`l = m₀ ‖ m₁` only (`chRun_congr`). On `z = ⟨pk, Enc(β; re)⟩` with seed blocks `v`, `D` runs `A`
answering the planted tuple `W β v re l` (`plantTuple_spec`) and outputs
`(l_j ≠ l_{n+j}) ∧ (a ≠ l_j)` (`plantOut_recorded`), or `0` without a challenge
(`plantOut_init`). Resampling coin block `j` (`expect_sample_update`) turns hybrid `j` into
`W (l_j)` and hybrid `j + 1` into `W (l_{n+j})` (`hybCt_update`), and the case split on
`(l_j, l_{n+j})` (`expect_indicator_sub`) matches the two differences. -/
private theorem hyb_advantage_eq {S : BitPublicKeyScheme} (L : PolyExpr)
    (hL : ∀ n (rg : S.bitwise.gen.Coins n) (m : Fin n → Bool) (re : S.bitwise.enc.Coins n),
      2 * (S.bitwise.enc.runAt n (pairEncode (pairFstD (S.bitwise.gen.runAt n [] rg))
        (List.ofFn m)) re).length + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n) (A : NUPPT) (q : PolyExpr) (js : ℕ → ℕ) (D : NUPPT) (n : ℕ)
    (hj : js n < n)
    (φ : (Fin ((PolyExpr.mul .var S.enc.coins).eval n) → Bool) × A.Coins n ≃ D.Coins n)
    (hφ : ∀ (ins outs : Fin 2 → ℕ), (fun i => (qDin L (.add .var .var) i).eval n) = ins →
      (fun i => (qDout (.add .var (.const 1)) L i).eval n) = outs →
      ∀ (z : List Bool) (ω : Fin ((PolyExpr.mul .var S.enc.coins).eval n) → Bool)
        (r : A.Coins n),
        (∀ y : List Bool, y.length = (PolyExpr.add .var .var).eval n →
          (plantAns S.enc L (pairEncode (seedIn n z (List.ofFn ω))
            (pairEncode (bwAux S js n) y))).length = L.eval n) →
        D.runAt n z (φ (ω, r)) =
          plantOut (pairEncode (seedIn n z (List.ofFn ω))
            (pairEncode (pairEncode (bwAux S js n)
              ((firstQ (A.toCompOn (bitCodec ins outs 1) n (q.eval n) (pairFstD z) r)).elim
                (false :: List.replicate ((PolyExpr.add .var .var).eval n) false) (true :: ·)))
              (List.ofFn (chRun (fun y => plantAns S.enc L (pairEncode (seedIn n z (List.ofFn ω))
                  (pairEncode (bwAux S js n) (List.ofFn y))))
                (A.toCompOn (bitCodec ins outs 1) n (q.eval n) (pairFstD z) r) none).1)))) :
    advantage (hybGame S L hL hmsg A (q.eval n) n (js n))
        (hybGame S L hL hmsg A (q.eval n) n (js n + 1)) =
      distAdv (S.pkEncDist n false) (S.pkEncDist n true) (D.distinguisherL n) := by
  -- Notation: the game's computation, `A`'s bit, and the planted padded tuple.
  let comp : S.gen.Coins n → A.Coins n →
      OracleComp ((S.bitwise.padded L hL hmsg).indSpec n) (Fin 1 → Bool) := fun rg r =>
    A.toCompOn ((S.bitwise.padded L hL hmsg).indCodec n) n (q.eval n)
      (pairFstD (S.gen.runAt n [] rg)) r
  let F : S.gen.Coins n → A.Coins n → List Bool → Bool := fun rg r w =>
    (chRun (fun _ => w) (comp rg r) none).1 0
  let W : Bool → S.gen.Coins n → (Fin n → S.enc.Coins n) → S.enc.Coins n → List Bool →
      List Bool := fun β rg v re l =>
    padCt (L.eval n) (PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n =>
      if (i : ℕ) < js n then
        S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [l.getD (n + i) false]) (v i)
      else if (i : ℕ) = js n then
        S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [β]) re
      else S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [l.getD i false]) (v i)))
  -- The handler's lengths are the game's.
  have hins : (fun i => (qDin L (.add .var .var) i).eval n) =
      (S.bitwise.padded L hL hmsg).inLens n := by
    funext i
    match i with
    | 0 => rw [qDin_zero, FixedLengthPKScheme.inLens_zero, PublicKeyScheme.padded_ctLen]
    | 1 =>
      rw [qDin_one, FixedLengthPKScheme.inLens_one, PublicKeyScheme.padded_msgLen,
        PolyExpr.eval_add]
  have houts : (fun i => (qDout (.add .var (.const 1)) L i).eval n) =
      (S.bitwise.padded L hL hmsg).outLens n := by
    funext i
    match i with
    | 0 =>
      rw [qDout_zero, FixedLengthPKScheme.outLens_zero, PublicKeyScheme.padded_msgLen,
        PolyExpr.eval_add, PolyExpr.eval_const]
    | 1 => rw [qDout_one, FixedLengthPKScheme.outLens_one, PublicKeyScheme.padded_ctLen]
  -- The seed is `n` coin blocks.
  let seedE : (Fin n → S.enc.Coins n) ≃ (Fin ((PolyExpr.mul .var S.enc.coins).eval n) → Bool) :=
    (coinBlocks n (S.enc.coinLen n)).trans
      (Equiv.arrowCongr (finCongr (S.bitwise_enc_coinLen n)) (Equiv.refl Bool))
  have hseed : ∀ v, List.ofFn (seedE v) = List.ofFn (coinBlocks n (S.enc.coinLen n) v) :=
    fun v => (List.ofFn_congr (S.bitwise_enc_coinLen n) _).symm
  have hL' : ∀ (rg : S.gen.Coins n) (m : Fin n → Bool) (re : S.bitwise.enc.Coins n),
      2 * (S.bitwise.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m))
        re).length + 2 ≤ L.eval n := by
    have h := hL n
    rw [BitPublicKeyScheme.bitwise_gen] at h
    exact h
  -- The handler's answer to a challenge `l` is the planted padded tuple.
  have hans : ∀ (β : Bool) (rg : S.gen.Coins n) (re : S.enc.Coins n) (v : Fin n → S.enc.Coins n)
      (l : List Bool), l.length = n + n →
      plantAns S.enc L (pairEncode (seedIn n (S.pkEncDist n β (rg, re)) (List.ofFn (seedE v)))
        (pairEncode (bwAux S js n) l)) = W β rg v re l := by
    intro β rg re v l hl
    rw [plantAns_eq, BitPublicKeyScheme.pkEncDist_eq, hseed v, bwAux]
    conv_lhs => rw [ofFn_getD_split l hl]
    rw [plantTuple_spec S.enc S.enc_uniform n (js n) hj, seedIn_eq, pairFstD_pairEncode,
      pairFstD_pairEncode, List.length_replicate]
  have hw : ∀ (β : Bool) (rg : S.gen.Coins n) (re : S.enc.Coins n) (v : Fin n → S.enc.Coins n)
      (y : List Bool), y.length = (PolyExpr.add .var .var).eval n →
      (plantAns S.enc L (pairEncode (seedIn n (S.pkEncDist n β (rg, re)) (List.ofFn (seedE v)))
        (pairEncode (bwAux S js n) y))).length = L.eval n := by
    intro β rg re v y hy
    rw [PolyExpr.eval_add, PolyExpr.eval_var] at hy
    rw [hans β rg re v y hy]
    show (padCt (L.eval n) _).length = L.eval n
    refine length_padCt ?_
    rw [planted_eq S n (js n) hj, ← bitwise_runAt_blocks]
    exact hL' rg _ _
  -- Step 3, distinguisher side: `D`'s verdict.
  have hpt : ∀ (β : Bool) (rg : S.gen.Coins n) (r : A.Coins n) (re : S.enc.Coins n)
      (v : Fin n → S.enc.Coins n),
      D.distinguisherL n (S.pkEncDist n β (rg, re)) (φ (seedE v, r)) =
        (firstQ (comp rg r)).elim false fun l =>
          (l.getD (js n) false != l.getD (n + js n) false) &&
            (F rg r (W β rg v re l) != l.getD (js n) false) := by
    intro β rg r re v
    have hz : pairFstD (S.pkEncDist n β (rg, re)) = pairFstD (S.gen.runAt n [] rg) := by
      rw [BitPublicKeyScheme.pkEncDist_eq, pairFstD_pairEncode]
    have ha : List.ofFn (chRun (fun y => plantAns S.enc L (pairEncode
        (seedIn n (S.pkEncDist n β (rg, re)) (List.ofFn (seedE v)))
          (pairEncode (bwAux S js n) (List.ofFn y))))
        (A.toCompOn ((S.bitwise.padded L hL hmsg).indCodec n) n (q.eval n)
          (pairFstD (S.gen.runAt n [] rg)) r) none).1 =
        [F rg r ((firstQ (comp rg r)).elim [] fun l => plantAns S.enc L (pairEncode
          (seedIn n (S.pkEncDist n β (rg, re)) (List.ofFn (seedE v)))
            (pairEncode (bwAux S js n) l)))] := by
      rw [chRun_congr _ (fun _ => (firstQ (comp rg r)).elim [] fun l => plantAns S.enc L
        (pairEncode (seedIn n (S.pkEncDist n β (rg, re)) (List.ofFn (seedE v)))
          (pairEncode (bwAux S js n) l))) _ fun mm hmm => by rw [hmm, Option.elim_some],
        List.ofFn_succ, List.ofFn_zero]
    have hrun : D.runAt n (S.pkEncDist n β (rg, re)) (φ (seedE v, r)) =
        [(firstQ (comp rg r)).elim false fun l =>
          (l.getD (js n) false != l.getD (n + js n) false) &&
            (F rg r (W β rg v re l) != l.getD (js n) false)] := by
      rw [hφ _ _ hins houts _ _ _ (hw β rg re v), hz, ← AdaptiveCPA.indCodec_eq_bitCodec, ha]
      cases hq : firstQ (comp rg r) with
      | none => simp only [Option.elim_none, plantOut_init]
      | some l =>
        have hl : l.length = n + n := by
          rw [length_of_firstQ_eq_some _ hq, FixedLengthPKScheme.inLens_one,
            PublicKeyScheme.padded_msgLen, PolyExpr.eval_var]
        simp only [Option.elim_some]
        rw [hans β rg re v l hl, bwAux, plantOut_recorded, List.headD_cons]
    rw [NUPPT.distinguisherL_eq, hrun]
    generalize ((firstQ (comp rg r)).elim false fun l =>
      (l.getD (js n) false != l.getD (n + js n) false) &&
        (F rg r (W β rg v re l) != l.getD (js n) false)) = x
    cases x <;> rfl
  have hD : ∀ β : Bool, acceptProb (S.pkEncDist n β) (D.distinguisherL n) =
      expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
        expect (ProbComp.sample (A.Coins n)) fun r =>
          expect (ProbComp.sample (Fin n → S.enc.Coins n)) fun v =>
            expect (ProbComp.sample (S.enc.Coins n)) fun re =>
              if ((firstQ (comp rg r)).elim false fun l =>
                (l.getD (js n) false != l.getD (n + js n) false) &&
                  (F rg r (W β rg v re l) != l.getD (js n) false)) = true then 1 else 0 := by
    intro β
    rw [Bridge.acceptProb_eq, accept_eq, Bridge.acceptGame_eq, prob_bind, expect_sample_prod]
    refine congrArg _ (funext fun rg => ?_)
    simp only [prob_bind, prob_pure]
    rw [expect_sample_comm, ← expect_sample_equiv φ, expect_sample_prod, expect_sample_comm]
    refine congrArg _ (funext fun r => ?_)
    rw [← expect_sample_equiv seedE]
    refine congrArg _ (funext fun v => congrArg _ (funext fun re => ?_))
    rw [hpt β rg r re v]
  -- Step 3, hybrid side: only the first challenge matters.
  have hH : ∀ j' : ℕ, accept (hybGame S L hL hmsg A (q.eval n) n j') =
      expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
        expect (ProbComp.sample (A.Coins n)) fun r =>
          expect (ProbComp.sample (Fin n → S.enc.Coins n)) fun v =>
            if F rg r ((firstQ (comp rg r)).elim [] fun l =>
              padCt (L.eval n) (hybCt S n j' (pairFstD (S.gen.runAt n [] rg)) v l)) = true
            then 1 else 0 := by
    intro j'
    rw [accept_eq]
    unfold hybGame
    rw [prob_bind]
    refine congrArg _ (funext fun rg => ?_)
    rw [prob_bind]
    refine congrArg _ (funext fun r => ?_)
    rw [prob_bind]
    refine congrArg _ (funext fun v => ?_)
    rw [prob_pure]
    congr 2
    exact congrArg (fun p : (Fin 1 → Bool) ×
        Option (Fin ((S.bitwise.padded L hL hmsg).outLens n 1) → Bool) => p.1 0)
      (chRun_congr _ _ _ fun mm hmm => by rw [hmm, Option.elim_some])
  -- Assemble: both differences are `𝔼_{rg, r}` of equal pointwise differences.
  rw [advantage_eq, distAdv_def, hH (js n), hH (js n + 1), hD false, hD true]
  congr 1
  rw [← expect_sub]
  conv_rhs => rw [← expect_sub]
  refine congrArg _ (funext fun rg => ?_)
  rw [← expect_sub]
  conv_rhs => rw [← expect_sub]
  refine congrArg _ (funext fun r => ?_)
  cases hq : firstQ (comp rg r) with
  | none => simp only [Option.elim_none, Bool.false_eq_true, if_false, sub_self]
  | some l =>
    simp only [Option.elim_some]
    rw [← expect_sample_update (⟨js n, hj⟩ : Fin n) (fun v => if F rg r (padCt (L.eval n)
        (hybCt S n (js n) (pairFstD (S.gen.runAt n [] rg)) v l)) = true then (1 : ℝ) else 0),
      ← expect_sample_update (⟨js n, hj⟩ : Fin n) (fun v => if F rg r (padCt (L.eval n)
        (hybCt S n (js n + 1) (pairFstD (S.gen.runAt n [] rg)) v l)) = true then (1 : ℝ) else 0)]
    have h₀ := fun v re =>
      hybCt_update S n (js n) hj (pairFstD (S.gen.runAt n [] rg)) v re l false
    have h₁ := fun v re =>
      hybCt_update S n (js n) hj (pairFstD (S.gen.runAt n [] rg)) v re l true
    simp only [Bool.false_eq_true, if_false, if_true] at h₀ h₁
    simp only [h₀, h₁]
    have key := expect_indicator_sub (ρ := (Fin n → S.enc.Coins n) × S.enc.Coins n)
      (fun β p => F rg r (W β rg p.1 p.2 l)) (l.getD (js n) false) (l.getD (n + js n) false)
    rw [expect_sample_prod, expect_sample_prod, expect_sample_prod, expect_sample_prod] at key
    exact key

end BitwiseCPAProof

/-- **The padded bitwise scheme is CPA-secure** when its single-bit scheme is secure
[PS10, the hybrid argument of p. 103, in the CPA game of Definition 171.5]. The bound `hL`
covers every ciphertext of the bitwise scheme, so `S.bitwise.padded L hL hmsg` has `n`-bit
messages and `L(n)`-bit ciphertexts.

**Proof sketch.**
1. Fix `A` and `q`. For `j ≤ n` let `H_j` be the CPA experiment whose challenge encrypts, bit by
   bit with independent coins `v_i`, the first `j` bits of the right message and the remaining
   bits of the left message (`hybGame`, with the encryption coins sampled in advance). `H_0` and
   `H_n` have the acceptance probabilities of the experiments with `b = false` and `b = true`
   (`accept_indGame_eq`: eager coins `BitwiseSim.expect_simulate_indImpl_cpa`, the bitwise
   layout `bitwise_enc_runAtL` and the coin blocks `bitwiseEncCoins_ofFn`).
2. By `Games.exists_advantage_hybrid_gap`, at each `n > 0` some `j⋆(n) < n` has
   `advantage(H_{j⋆}, H_{j⋆+1}) ≥ advantage(H_0, H_n) / n`; at `n = 0` the two ends coincide and
   the advantage is `0`.
3. The distinguisher `D` on `⟨pk, c⟩` runs `A` on `pk`, answers every `Dec` query with `⊥`, answers
   the first challenge `⟨m₀, m₁⟩` (and every later one) with the padded bitwise ciphertext whose
   block `j⋆` is `c` and whose other blocks it encrypts itself (bits of `m₁` before `j⋆`, of `m₀`
   after) on `pk` and its seed of `n` single-bit encryption tapes (`BitwiseSim.plantAns`), and
   outputs `A`'s bit, flipped when `(m₀_{j⋆}, m₁_{j⋆}) = (1, 0)` and replaced by `0` when the two
   bits agree or no challenge was asked (`BitwiseSim.plantOut`). `D` is a machine by T1 for the
   query-recording handler with `j⋆(n)` in its initial state (`BitwiseSim.exists_qHandlerMachine`).
   Then `advantage(H_{j⋆}, H_{j⋆+1})` equals `D`'s single-bit advantage between `⟨pk, Enc_pk(0)⟩`
   and `⟨pk, Enc_pk(1)⟩` exactly (`hyb_advantage_eq`): only the first challenge matters
   (`ChallengeSim.chRun_congr`); resampling coin block `j⋆` turns the two hybrids into the
   planted tuples with `Enc(m₀_{j⋆})` and `Enc(m₁_{j⋆})` (`BitwiseSim.expect_sample_update`); and
   the signed case split on `(m₀_{j⋆}, m₁_{j⋆})` is `ChallengeSim.expect_indicator_sub`.
4. So `A`'s advantage is at most `n` times `D`'s advantage, negligible by `singleBitSecure_iff`;
   the product is negligible by `Negligible.polyExpr_mul` with `PolyExpr.var`. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.bitwise_padded_cpa
    {S : BitPublicKeyScheme} (h : S.SingleBitSecure) (L : PolyExpr)
    (hL : ∀ n (rg : S.bitwise.gen.Coins n) (m : Fin n → Bool) (re : S.bitwise.enc.Coins n),
      2 * (S.bitwise.enc.runAt n (pairEncode (pairFstD (S.bitwise.gen.runAt n [] rg))
        (List.ofFn m)) re).length + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n) : (S.bitwise.padded L hL hmsg).INDSecure .cpa := by
  rw [FixedLengthPKScheme.INDSecure_iff]
  intro A q
  -- Steps 1–2: the hybrids and, for `n > 0`, an index `j⋆(n) < n` of a largest gap.
  have hgap : ∀ n, ∃ j ≤ n, 0 < n → j < n ∧
      advantage (hybGame S L hL hmsg A (q.eval n) n 0) (hybGame S L hL hmsg A (q.eval n) n n) /
          n ≤
        advantage (hybGame S L hL hmsg A (q.eval n) n j)
          (hybGame S L hL hmsg A (q.eval n) n (j + 1)) := by
    intro n
    by_cases hn : 0 < n
    · obtain ⟨j, hj, hgj⟩ := exists_advantage_hybrid_gap (hybGame S L hL hmsg A (q.eval n) n) hn
      exact ⟨j, hj.le, fun _ => ⟨hj, hgj⟩⟩
    · exact ⟨0, Nat.zero_le _, fun h => absurd h hn⟩
  choose js hjle hjs using hgap
  -- Step 2: the distinguisher `D`, by T1 for the query-recording handler.
  obtain ⟨D, hD⟩ := BitwiseSim.exists_qHandlerMachine A q L (.add .var .var) (.add .var (.const 1))
    (bwLaux S) (.mul .var S.enc.coins) (bwAux S js) (bwAux_length S js hjle)
    (BitwiseSim.plantAns S.enc L) (BitwiseSim.polyTimeComputable_plantAns S.enc L)
    BitwiseSim.plantOut BitwiseSim.polyTimeComputable_plantOut
  refine ⟨fun n => (PolyExpr.var.eval n : ℝ) *
      distAdv (S.pkEncDist n false) (S.pkEncDist n true) (D.distinguisherL n),
    ((BitPublicKeyScheme.singleBitSecure_iff S).1 h D).polyExpr_mul .var, fun n => ?_⟩
  -- Step 1: the ends of the hybrids are the two games.
  rw [advantage_eq, accept_indGame_eq, accept_indGame_eq, ← advantage_eq]
  simp only [Bool.false_eq_true, ↓reduceIte, PolyExpr.eval_var]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [advantage_eq, sub_self, abs_zero, Nat.cast_zero, zero_mul]
  · -- Steps 3–4: the exact identity and the bound `n · ε(n)`.
    obtain ⟨φ, hφ⟩ := hD n
    rw [← hyb_advantage_eq L hL hmsg A q js D n (hjs n hn).1 φ hφ]
    have h1 := (hjs n hn).2
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hn'] at h1
    linarith

/-- **The padded bitwise scheme is adaptively CPA-secure** when its single-bit scheme is secure:
`bitwise_padded_cpa` followed by the hybrid lifting
`Composability.FixedLengthPKScheme.INDSecure.adaptive_cpa`. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.bitwise_padded_adaptive_cpa
    {S : BitPublicKeyScheme} (h : S.SingleBitSecure) (L : PolyExpr)
    (hL : ∀ n (rg : S.bitwise.gen.Coins n) (m : Fin n → Bool) (re : S.bitwise.enc.Coins n),
      2 * (S.bitwise.enc.runAt n (pairEncode (pairFstD (S.bitwise.gen.runAt n [] rg))
        (List.ofFn m)) re).length + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n) : (S.bitwise.padded L hL hmsg).AdaptiveINDSecure .cpa :=
  (h.bitwise_padded_cpa L hL hmsg).adaptive_cpa

/-- **A secure single-bit scheme yields an adaptively CPA-secure scheme with `n`-bit messages**:
some fixed-length scheme with message length `PolyExpr.var` and the same key generator is
secure in the adaptive multi-challenge CPA game. The padding bound comes from
`PublicKeyScheme.exists_padBound`.

**Proof sketch.** Take `L`, `hL` and `hmsg` from `S.bitwise.exists_padBound`; the witness is
`S.bitwise.padded L hL hmsg` (`PublicKeyScheme.padded_msgLen`, `PublicKeyScheme.padded_gen`, and
the generator of `S.bitwise` is `S.gen`), secure by `bitwise_padded_adaptive_cpa`. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.exists_adaptive_cpa
    {S : BitPublicKeyScheme} (h : S.SingleBitSecure) :
    ∃ S' : FixedLengthPKScheme, S'.msgLen = .var ∧ S'.gen = S.gen ∧
      S'.AdaptiveINDSecure .cpa := by
  obtain ⟨L, hL, hmsg⟩ := S.bitwise.exists_padBound
  exact ⟨S.bitwise.padded L hL hmsg, PublicKeyScheme.padded_msgLen _ _ _ _,
    (PublicKeyScheme.padded_gen _ _ _ _).trans (BitPublicKeyScheme.bitwise_gen S),
    h.bitwise_padded_adaptive_cpa L hL hmsg⟩

end TCSlib.Cryptography.Composability
