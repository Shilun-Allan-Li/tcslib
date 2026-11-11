## ===== briefs/pass-shelat-ch5-8/gates/12-cpa-pilot/pack.md =====

# Gate 12 · CPA pilot statements

Round 1. Auditor Codex. Draft [PR #287](https://github.com/Shilun-Allan-Li/tcslib/pull/287) at
`135d54511dc0e5c42d93d1d680bf1f26c6aba5cc` on branch `maint/pass-shelat-cpa-pilot`, targeting
`cryptography/pass-shelat-ch2-4` on base `ed0f723871e0fd65e674bcf3f55c7e0ee173fdf5` (the campaign
after #284–#286).

This is a **statement audit**. It runs before any fill. It covers the two admitted statements,
the two corollaries proved from them, and three new reader lemmas. These are the first steps of
the Implications endpoint "multi-message IND-CPA public-key encryption". Seyoon ruled on
2026-11-11 for the route: two generic theorems, then compose. The endpoint game is
`FixedLengthPKScheme.AdaptiveINDSecure` (Gate 09, merged in #284), and it is not changed here.
The source is [PS10], R. Pass and a. shelat, *A Course in Cryptography*, third edition,
January 2010: Definition 171.5, and Algorithm 104.3 with Theorem 104.4 and p. 103.

## What to check

1. **`FixedLengthPKScheme.INDSecure.adaptive_cpa`** (`PublicKey/AdaptiveCPA.lean`).
   - Is it true for every `FixedLengthPKScheme`, with exactly these hypotheses?
   - Check the cap semantics of `adaptiveIndImpl`: a challenge past the cap repeats the latest
     ciphertext; with cap 0 the reply is zero. Check also the history-based refusal of `Dec`
     (vacuous under CPA), a zero cap, and polynomial `q` and `cap`.
   - Is the hybrid sketch sound? In particular:
     - the endpoints `H_0` and `H_cap` equal the `b = false` and `b = true` experiments;
     - the advice index `i⋆(n)` comes from `exists_advantage_hybrid_gap`;
     - the reduction is built by T2 (`exists_interactiveHandlerMachine`), with its outer-query
       budget;
     - the `cap(n)` factor is handled by `Negligible.polyExpr_mul`.
   - Can a fill complete it through published interfaces only? Name any missing reader.
2. **`BitPublicKeyScheme.SingleBitSecure.bitwise_padded_cpa`** (`PublicKey/BitwiseCPA.lean`).
   - Is it true, with the padding bound `hL` for `S.bitwise` and `hmsg : n ≤ L(n)`?
   - The adversary chooses its messages after seeing the public key. The module docstring says
     that n-bit ensemble `Secure`, whose messages are fixed in advance, would not suffice. Is that
     right, and is single-bit security the right premise?
   - Check the bit-hybrid sketch: the endpoint hybrids `H_0` and `H_n`, `n = 0`, and the reduction
     `D` on `⟨pk, c⟩` with its flip/zero output rule. `D` is built through T1, with `j⋆(n)` in
     the initial state and `n` encryption tapes as its seed. Check also the exact single-bit
     identity, and the coin layout of the bitwise encryptor (`bitwise_enc_runAt`,
     `bitwiseEncCoins_ofFn`).
3. **The corollaries.** `bitwise_padded_adaptive_cpa` and `exists_adaptive_cpa` are proved from the
   two targets.
   - Does `exists_adaptive_cpa` state a meaningful catalog-ready guarantee: `msgLen = .var`, the
     same key generator, adaptive CPA?
   - Is anything missing that the RSA and Rabin catalog theorems will need, such as correctness
     and efficiency? Those are carried by `FixedLengthPKScheme`.
4. **Readers.** `bitwise_gen`, `bitwise_enc` and `bitwise_dec` must state the definition exactly.
   Each should be public, not `@[simp]`, and have a docstring with its formula.
5. **Rule 10 and duplication.**
   - No statement or proof reads another file's definition. The evidence includes a seal probe of
     both corollaries with a control.
   - Nothing duplicates an existing public TCSlib or Mathlib result. Compare with
     `PublicKeyScheme.Secure.multiMessageSecure`, `SingleBitSecure.bitwise` and
     `AdaptiveINDSecure.single`.
6. **Placement, imports, facade exports and docstrings.** Policy §§1–3 apply.

## Evidence (`evidence/`)

- `replay.jsonl`, `replay-order.txt`: the 15 modules downstream of the change, rc 0, through the
  library root and `audits/pass-shelat/Checks`. `sorry` warnings are exactly the two targets.
  `replay-after-docfix.jsonl` rechecks the 8 modules after the final docstring wrap.
- `SealProbe.lean`, `seal-probe.log`: both corollaries elaborate with `padded`, `bitwise`,
  `ofPadded`, `INDSecure`, `AdaptiveINDSecure`, `SingleBitSecure`, `runAt`, `pairEncode` and
  `pairFstD` sealed. The only error is the intended control at line 27, which reads `bitwise`
  through its body.
- `axioms.log`: the readers use standard axioms. `exists_adaptive_cpa` additionally depends on
  `sorryAx` through the two admitted targets, as intended.

## Findings delivery

Return `gate12-cpa-pilot-findings.md` as a Markdown file in this chat. For multiple evidence
files, return a ZIP. The user dispatches and merges.

| # | Severity | File and declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

Severities:
- **blocker:** a false or unusable statement, or a scope violation;
- **major:** a missing hypothesis, a statement too weak or too strong for its consumers, a
  forbidden read, a duplicate public result, or necessary evidence that cannot be verified;
- **minor:** documentation or API defects;
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero
majors.

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

## ===== briefs/pass-shelat-ch5-8/PROOFS-AND-IMPLICATIONS-PLAN.md =====

# Pass–shelat proof and Implications plan

Planning base `0cb228f06ae56e91bc903cae801e49db73e0ae23` on `cryptography/pass-shelat-ch2-4`, after the merge of
[#282](https://github.com/Shilun-Allan-Li/tcslib/pull/282). This is the proof
roadmap for chapters 2–4 and the additional encryption material. The proof,
interface, and catalog PRs target the campaign branch. Revisit a release to
`main` after the selected proofs and the release-scope seals are complete.
Secure computation reorganization remains a later layout phase.

## 1. Refresh the proof prerequisites

Pin each proof batch to the current source, its dependency closure, and the
frozen statement headers. Use the [#248 acceptance record](maintainer/cleanup-incremental-2026-11-09/final-r1/README.md)
and the relocation records to identify retained reads and their current
owners. The [earlier dependency screen](maintainer/proof-dependency-screen-2026-11-08/README.md)
predates #248 and the import moves. Repeat it on the intended base before
assigning work, then inspect the actual reader dependencies of each route.

Start with the [efficiency draft](fills/efficiency/brief-draft.md). Its
candidate prerequisites now have public names in
[`PPT`](../../TCSlib/Complexity/Randomized/PPT.lean) and
[`Functions.Asymptotic.Defs`](../../TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/Defs.lean).
Probe `NUPPT.coinLen_eq` and the complete `decodeOracleMove` case split,
including malformed words and wrong-length payloads. Check the shared
`decodeFin_eq_some_iff` reader and the existing GGM loop equations at their
current owners. Run the toy handler and zero-width codec probes specified
in the draft. Record which providers are ready and request a scoped ruling
if an efficiency fill would need a dependency with unresolved cleanup reads.
The [cleanup plan](CLEANUP-PLAN.md#3-close-the-inherited-seal-ledger-on-the-new-layout)
continues to govern the full seal pass.

In parallel, preflight the fixed-length PRF CCA2 separation and the two Levin
proofs below. The separation sketch uses a directly constructed uniform
adversary. It is the first candidate for a small independent proof PR if
its reader and ownership checks pass. Endpoint statement design can proceed
alongside these probes.

## 2. Fill the existing proofs

The Gate 06 encryption headers landed in
[#232](https://github.com/Shilun-Allan-Li/tcslib/pull/232). Fill the frozen
statements through their published interfaces. Route changes can refresh
the proof sketch. A substantive statement change gets a separate audit.

| Batch | Targets and dependencies |
| --- | --- |
| Shared machine reductions | Fill `exists_handlerMachine` (T1), `exists_interactiveHandlerMachine` (T2), `exists_toCompOn_of_toComp` and `exists_toOracleAdversary_of_bitCodec` (T4). Prioritize the plain handler for public-key CPA. The interactive handler, input-free companion and codec transport are the route in the private-key CPA and CCA sketches. Reuse the GGM loop and check the resulting machine's run law, coins, and query budget. Keep one owner for the batch. [Source](../../TCSlib/Cryptography/Games/Efficiency.lean) · [Design](design/S2b-efficiency.md) |
| Private-key oracle security | Fill `prfFixedScheme_not_cca2` as the independent candidate. Then prove `prfFixedScheme_cpa` and `prfFixedScheme_cca1` using the checked handler and codec path. Fill `ccaScheme_cca2` after CPA and the shared reductions pass. The tagged proof needs the first-discrepancy bound and exact challenge refusal in its game. Check that the derived `not_prfFixedScheme_cca2` also has only standard axioms. [Fixed-length PRF scheme](../../TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF.lean) · [Encrypt-then-tag](../../TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag.lean) |
| Public-key CPA bridge | Fill `BitPublicKeyScheme.SingleBitSecure.padded_cpa` after T1 or a checked equivalent route. Preserve the padding bound, the public-key-dependent message choice, and the machine run agreement. Recheck `TrapdoorCollection.tdpBitScheme_padded_cpa`, which inherits the bridge. This is the CPA dependency for the first catalog route. [Oracle security](../../TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean) · [Trapdoor corollary](../../TCSlib/Cryptography/Encryption/PublicKey/TrapdoorCPA.lean) |
| Public-key non-malleability | Prove `indSecure_cca2_iff_nmSecure_cca2`, `nmSecure_of_simNMSecure`, and `simNMSecure_of_nmSecure_cpa` against the audited formulations. Check which shared handlers each proof needs and preserve the attack quantifiers and simulator interface. Recheck the derived simulation/IND non-malleability equivalence at CPA. [Indistinguishability](../../TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability.lean) · [Simulation](../../TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation.lean) |
| Levin universal one-way function | Scope two machine proofs separately. `PadQuad.exists_linearTime_gStr` needs a registered or reused construction with the exact linear time bound on all inputs. Its completion clears the admission in `lemma_64_3` and then `theorem_63_1`. `exists_canonizerExp` needs a concrete `EffectiveMachineCode` and a bound for its canonizer, including malformed inputs. The conditional Levin theorems keep their stated `CanonizerExp` premise. [Padding machine](../../TCSlib/Cryptography/Asymptotic/UniversalPadding.lean) · [Canonizer and theorem](../../TCSlib/Cryptography/Asymptotic/Universal.lean) |

The shared reductions and the public-key CPA bridge are the proof critical
path for the CPA route. The non-malleability and Levin batches can advance
on their own owners when the dependency screen clears. The chapter 2–4
statement audits `03d`, `03h`, `03i`, `03j`, and `03k` still need restaging
on current owners after their recorded prerequisites. [Audit status](MAINTAINER-HANDOFF.md#6-current-state-verified-at-codex-intake-2026-11-06-pst)

### Additional proof packages

- The optional `NUPPT.decides_of_decidesWithAdviceInTime` bridge needs a
  clocked simulation with agreement on the well-formed advised inputs.
  Decide its release scope separately from the two Levin targets.
  [Advice bridge](../../TCSlib/Complexity/Randomized/NonUniform.lean)
- Queue `prfMAC_secure`, `lamport_oneTimeSecure`, `hashAndSign_oneTimeSecure`,
  and `dlHash_crh` as authentication and hashing work. The current sketches
  put the PRF-MAC after the interactive handler and codec path, Lamport after
  the plain handler, and hash-and-sign after its plain and interactive
  reductions. Check the generic hash-and-sign result and its Lamport
  composition separately. Screen the discrete-log hash proof as its own
  route. [MAC](../../TCSlib/Cryptography/Authentication/MAC/FromPRF.lean) ·
  [Lamport](../../TCSlib/Cryptography/Authentication/Signatures/Lamport.lean) ·
  [Hash-and-sign](../../TCSlib/Cryptography/Authentication/Signatures/HashAndSign.lean) ·
  [Discrete-log hash](../../TCSlib/Cryptography/Hashing/FromDiscreteLog.lean)

## 3. Define and prove the Implications endpoints

The selected public-key endpoints are **multi-message IND-CPA** and
**multi-message IND-CCA2**. CCA1 remains an intermediate. The final
theorems in `Cryptography/Implications/PublicKey.lean` start from explicit
sets of assumptions and produce a correct, efficient scheme with the chosen
security guarantee and a meaningful message space. Publish the game and
supporting proofs with their scheme owners and keep the catalog proofs as
short compositions through those interfaces.
[Implications design](implications/README.md)

### Settle the shared statement

Use `FixedLengthPKScheme` as the initial interface candidate. It already
packages uniform efficient key generation and encryption, efficient
decryption, and perfect correctness. Require a substantive message
space such as `n`-bit messages at positive security parameters, or state
the exact alternative and its size guarantee.

Propose a multi-challenge left-or-right experiment with one public key and
one hidden bit. An efficient adversary chooses pairs within a polynomial
query budget, and each challenge encryption uses fresh coins. Gate the
exact adversary and query semantics, including the one-challenge
specialization and how CCA2 handles adaptive decryption and all challenge
ciphertexts in the transcript. Bring the message-space and game choices
to Seyoon for a ruling before freezing the interface. The statement review
should cover repeated ciphertexts, malformed queries, and budget boundaries.
Publish the exact reduction and its machine cost before using the game in a
catalog theorem.
The existing `PublicKeyScheme.MultiMessageSecure` fixed-vector theorem
remains available in its own model.
[Fixed-vector game](../../TCSlib/Cryptography/Encryption/PublicKey/EnsembleSecurity.lean) ·
[Single-challenge oracle game](../../TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean)

### Deliver the CPA pilot first

1. With the public-key CPA bridge, package a meaningful fixed-length
   message scheme. Reuse the bitwise machinery where its contract applies.
   Check padding and unpadding, uniformity and fresh coins, and prove the
   transport to the audited oracle game, including the polynomial
   multi-challenge lift.
2. Develop the RSA/Rabin width transport in parallel. Gate a shared
   constant-shift collection contract and prove the generator, sampler
   and inverter run laws, closeness and one-wayness transports, and the
   candidate width equations. The design uses `n+2` for RSA and `n+3` for
   Blum Rabin to obtain exact `PolyExpr` widths. Reuse the existing
   negligibility and machine reparameterization facts. Move the general
   `Negligible.comp_of_le` to Foundations with its existing name and
   verify its consumers before lower-layer collection code uses it.
   Then compose Goldreich–Levin and the audited CPA endpoint.
   [Normalization design](implications/normalization-design.md)
3. Land the RSA composition first, then reuse the transport for Rabin.
   Keep `ArithmeticFP` and `RSAAssumption` explicit for RSA, and
   `ArithmeticFP`, `FactoringAssumption` and `BlumDensity` explicit for
   Rabin. Check each exact witness and all dependencies with `#print axioms`
   before exporting it. The catalog entry is the assumption-to-primitive
   theorem. The trapdoor and bitwise lemmas support it.
4. Follow with ElGamal after proving the message and game transport from
   `GroupPKScheme`. Retain its safe-prime generator, DDH and exceptional
   probability premises. For LWE, coordinate the parameter, correctness,
   efficiency and oracle-game bridges with the lattice owners. The
   existing finite Regev correctness and advantage theorems can be
   documented at their actual proved scope while that work proceeds.
   [ElGamal](../../TCSlib/Cryptography/Encryption/PublicKey/ElGamal.lean) ·
   [Lattice plan](../../LatticeCryptographyPlan.md)

### Treat public-key CCA2 as a construction milestone

Design the CCA2 candidate after the shared endpoint statement is settled.
Bring a source-backed route and its dependency list to Seyoon for a ruling
before freezing the construction. The lattice plan's lossy/all-but-one
trapdoor route is one candidate. Its review must identify the exact lossiness
and inversion contracts, a
strongly unforgeable one-time signature with compatible parameter widths,
and a correctness guarantee that fits the scheme record. Keep every
auxiliary assumption explicit. An LWE-only implication needs a proved
discharge of the signature and any other supporting assumptions. Once a
route is chosen, gate its statements, prove correctness and security,
and check the CCA2 multi-challenge transport including challenge
ciphertext exclusion. The public-key non-malleability equivalences belong
to their relation proofs in section 2. The tagged construction belongs to
private-key encryption. [Lattice CCA2 design](../../LatticeCryptographyPlan.md#d6-cryptographic-trapdoors-and-cca2)

## 4. Review and land each slice

For each proof or endpoint PR, record the exact source, target headers,
owner and approved dependencies. Apply the [repository policy](../../policy.md)
for new shared hosts, attribution, public equations, and proof sketches.
Check affected modules serially with `scripts/lean_check_tree.sh`, including
the relevant facade, `TCSlib` and campaign Checks. Use instance-aware seals
and sensitivity controls for affected declarations, and inspect explicit
and generated foreign reads. Compare declaration types and actual axiom
sets through each new proof and its advertised corollaries. A completed
catalog entry has a checked nonvacuous witness, the audited game, and
standard Lean axioms only.

Before preparing an external audit or fill, record Seyoon's Codex or Claude
choice. Seyoon dispatches and merges. Keep each proof batch on a reviewable
campaign PR and update the decision log after verification. Close the
remaining release-scope seal ledger on the settled source before preparing
a `main` candidate.

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

## ===== TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveSecurity

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# From one challenge to adaptively many under chosen-plaintext attack

For a public-key scheme, security in the single-challenge CPA game of [PS10, Definition 171.5]
implies security in the adaptive left-or-right game with a polynomial number of fresh
challenges (`FixedLengthPKScheme.AdaptiveINDSecure`). The argument is the hybrid lifting of
[PS10, Theorem 104.4's proof] and of [Pas09, Theorem 2]: the adversary holds the public key, so
a reduction can produce every challenge but one itself.

## Main results

* `Composability.FixedLengthPKScheme.INDSecure.adaptive_cpa` (stated; a `sorry` under its
  sketch): single-challenge CPA security gives adaptive multi-challenge CPA security.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definition 171.5 (book p. 171) and the hybrid argument of Theorem 104.4 (book p. 104).
* [Pas09] R. Pass, *Cornell CS 6830, lecture 13* (2009), §1 and Theorem 2.
-/

namespace TCSlib.Cryptography.Composability.FixedLengthPKScheme

open Complexity Turing TCSlib.Cryptography.Games

/-- **Single-challenge CPA security gives adaptive multi-challenge CPA security**: if every
efficient adversary has negligible advantage in the CPA game with one challenge, then every
efficient adversary has negligible advantage in the adaptive left-or-right CPA game with a
polynomial challenge cap `cap(n)` and query budget `q(n)` [PS10, Definition 171.5; the hybrid
argument of Theorem 104.4].

**Proof sketch.**
1. Fix `A`, `q` and `cap`. For `i ≤ cap(n)` let `H_i` be the adaptive CPA experiment in which the
   first `i` fresh challenges encrypt the right message and the later ones the left message. Then
   `H_0` is the experiment with `b = false` and `H_{cap(n)}` the one with `b = true`: a challenge
   past the cap only repeats the latest ciphertext (`adaptiveIndImpl_challenge_full`), and under CPA
   `Dec` answers `⊥` whatever the history (`indImpl_dec_cpa`, `adaptiveIndImpl_dec_issued`).
2. By `Games.exists_advantage_hybrid_gap`, at each `n > 0` with `cap(n) > 0` some `i⋆(n) < cap(n)`
   has `advantage(H_{i⋆}, H_{i⋆+1}) ≥ advantage(H_0, H_{cap(n)}) / cap(n)`; the case `cap(n) = 0`
   has advantage `0`.
3. The single-challenge adversary `B` takes `i⋆(n)` as advice. On `pk` it runs `A`, answers `Dec`
   with `⊥`, answers the first `i⋆` fresh challenges with encryptions of the right message and
   the fresh challenges after the `(i⋆+1)`-st with encryptions of the left message, computed with
   `Enc` on `pk` and its own coins, forwards the `(i⋆+1)`-st to its own `Challenge` oracle, repeats
   the latest ciphertext past the cap, and outputs `A`'s bit. Then `B`'s game with bit `b` is
   `H_{i⋆+b}`. `B` is a non-uniform PPT playing the outer game by
   `Games.exists_interactiveHandlerMachine` (T2): the handler's state holds the challenge count,
   the latest ciphertext and `i⋆(n)` (its initial state, an arbitrary function of `n`), its seed
   is `cap(n)` encryption tapes, its one outer call is the `(i⋆+1)`-st challenge, and its run is
   polynomial-time because `Enc` is uniform and polynomial-time.
4. `B` makes at most `q(n)·perCall + finCall` outer queries, a polynomial, so `h` bounds its
   advantage by a negligible `ε`. Hence `A`'s advantage is at most `cap(n) · ε(n)`, negligible
   by `Negligible.polyExpr_mul` (`Asymptotic/ReductionSupport`) with the polynomial `cap`. -/
theorem INDSecure.adaptive_cpa {S : FixedLengthPKScheme} (h : S.INDSecure .cpa) :
    S.AdaptiveINDSecure .cpa := by
  sorry

end TCSlib.Cryptography.Composability.FixedLengthPKScheme

## ===== TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The bitwise scheme under chosen-plaintext attack

The bitwise scheme of [PS10, Algorithm 104.3 and p. 103] encrypts an `n`-bit message one bit at
a time with a single-bit scheme. Padded to fixed-length ciphertexts (`PublicKeyScheme.padded`),
it is a fixed-length scheme with `n`-bit messages. If the single-bit scheme is secure, the padded
bitwise scheme is CPA-secure in the game of [PS10, Definition 171.5], where the adversary chooses
its two messages after seeing the public key, and hence secure in the adaptive multi-challenge
game.

Ensemble security of the bitwise scheme for message pairs fixed in advance
(`BitPublicKeyScheme.SingleBitSecure.bitwise`) is not enough here: there the messages cannot
depend on the public key. The proof below therefore goes back to single-bit security.

## Main results

* `BitPublicKeyScheme.SingleBitSecure.bitwise_padded_cpa` (stated; a `sorry` under its sketch):
  the padded bitwise scheme is CPA-secure.
* `BitPublicKeyScheme.SingleBitSecure.bitwise_padded_adaptive_cpa`: and adaptively CPA-secure.
* `BitPublicKeyScheme.SingleBitSecure.exists_adaptive_cpa`: a fixed-length scheme with `n`-bit
  messages and the same key generator is adaptively CPA-secure.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Algorithm 104.3, Theorem 104.4 and p. 103; Definition 171.5 (book pp. 103–104, 171).
-/

namespace TCSlib.Cryptography.Composability

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-- **The padded bitwise scheme is CPA-secure** when its single-bit scheme is secure
[PS10, Theorem 104.4's hybrid argument, in the CPA game of Definition 171.5]. The bound `hL`
covers every ciphertext of the bitwise scheme, so `S.bitwise.padded L hL hmsg` has `n`-bit
messages and `L(n)`-bit ciphertexts.

**Proof sketch.**
1. Fix `A` and `q`. For `j ≤ n` let `H_j` be the CPA experiment whose challenge encrypts, bit by
   bit with independent coins, the first `j` bits of the right message and the remaining bits of
   the left message; `H_0` and `H_n` are the experiments with `b = false` and `b = true`.
2. By `Games.exists_advantage_hybrid_gap`, at each `n > 0` some `j⋆(n) < n` has
   `advantage(H_{j⋆}, H_{j⋆+1}) ≥ advantage(H_0, H_n) / n`; at `n = 0` the messages are empty and
   the advantage is `0`.
3. `H_{j⋆}` and `H_{j⋆+1}` differ only in the plaintext bit of block `j⋆`. As in
   `BitPublicKeyScheme.SingleBitSecure.padded_cpa`, the distinguisher `D` on `⟨pk, c⟩` runs `A` on
   `pk`, answers the challenge `⟨m₀, m₁⟩` with the padded bitwise ciphertext whose block `j⋆` is
   `c` and whose other blocks it encrypts itself (bits of `m₁` before `j⋆`, of `m₀` after) on
   `pk` and its own coins, and outputs `A`'s bit, flipped when `(m₀_{j⋆}, m₁_{j⋆}) = (1, 0)` and
   replaced by `0` when the two bits agree or no challenge was asked. Then
   `advantage(H_{j⋆}, H_{j⋆+1})` equals `D`'s single-bit advantage between `⟨pk, Enc_pk(0)⟩` and
   `⟨pk, Enc_pk(1)⟩` exactly (the first-challenge congruence and eager coins of `padded_cpa`). `D`
   is a non-uniform PPT by `Games.exists_handlerMachine` (T1), with `j⋆(n)` in the handler's
   initial state and `n` single-bit encryption tapes as its seed; the bitwise ciphertext layout is
   read through `bitwise_enc_runAt` and `bitwiseEncCoins_ofFn`.
4. So `A`'s advantage is at most `n` times a negligible function (`singleBitSecure_iff`),
   negligible by `Negligible.polyExpr_mul` with `PolyExpr.var`. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.bitwise_padded_cpa
    {S : BitPublicKeyScheme} (h : S.SingleBitSecure) (L : PolyExpr)
    (hL : ∀ n (rg : S.bitwise.gen.Coins n) (m : Fin n → Bool) (re : S.bitwise.enc.Coins n),
      2 * (S.bitwise.enc.runAt n (pairEncode (pairFstD (S.bitwise.gen.runAt n [] rg))
        (List.ofFn m)) re).length + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n) : (S.bitwise.padded L hL hmsg).INDSecure .cpa := by
  sorry

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

/-- The bitwise scheme keeps the key generator: `S.bitwise.gen = S.gen`. -/
theorem bitwise_gen (S : BitPublicKeyScheme) : S.bitwise.gen = S.gen := rfl

/-- The bitwise encryptor is the uniform machine of `bitwiseEncFun` with `n · B(n)` coins:
`S.bitwise.enc = NUPPT.ofPolyTimeUniform S.bitwiseEncFun_poly (.mul .var S.enc.coins)`. -/
theorem bitwise_enc (S : BitPublicKeyScheme) :
    S.bitwise.enc = NUPPT.ofPolyTimeUniform S.bitwiseEncFun_poly (.mul .var S.enc.coins) := rfl

/-- The bitwise decryptor decrypts block by block: `S.bitwise.dec = decListFun S.dec`. -/
theorem bitwise_dec (S : BitPublicKeyScheme) : S.bitwise.dec = decListFun S.dec := rfl

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

## ===== TCSlib/Cryptography/Encryption/PublicKey.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Encryption.PublicKey.Scheme
import TCSlib.Cryptography.Encryption.PublicKey.HybridMachine
import TCSlib.Cryptography.Encryption.PublicKey.Hybrid
import TCSlib.Cryptography.Encryption.PublicKey.EnsembleSecurity
import TCSlib.Cryptography.Encryption.PublicKey.TrapdoorPredictor
import TCSlib.Cryptography.Encryption.PublicKey.Trapdoor
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveSecurity
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA
import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA
import TCSlib.Cryptography.Candidates.RSA
import TCSlib.Cryptography.Candidates.Rabin
import TCSlib.Cryptography.Candidates.DDH
import TCSlib.Cryptography.Encryption.PublicKey.ElGamal
import TCSlib.Cryptography.Encryption.PublicKey.Regev
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.FromPermutation
import TCSlib.Cryptography.Encryption.PublicKey.TrapdoorCPA
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Public-key encryption

## Main definitions

`TCSlib.Cryptography.PublicKeyScheme` and `TCSlib.Cryptography.BitPublicKeyScheme`
give the ensemble interfaces. `TCSlib.Cryptography.Composability.FixedLengthPKScheme`
supports the oracle CPA, CCA1 and CCA2 games.

## Main results

`TCSlib.Cryptography.TrapdoorCollection.tdpBitScheme` packages a correct bit scheme.
`TCSlib.Cryptography.TrapdoorCollection.tdpBitScheme_singleBitSecure` proves security
given one-wayness, a hard-core predicate and its efficient evaluator.
`TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.bitwise` and
`TCSlib.Cryptography.PublicKeyScheme.Secure.multiMessageSecure` give fixed-vector
multi-message security.

## Contents

* `Scheme` defines the scheme interfaces and their correctness fields.
* `HybridMachine` builds the public-key hybrid reduction and its coin split.
* `Hybrid` proves the shared-key bound on tuples of encryptions.
* `EnsembleSecurity` gives the games, bitwise construction and fixed-vector security theorem.
* `TrapdoorPredictor` builds the machine used to predict the hard-core bit.
* `Trapdoor` proves correctness and single-bit security of Algorithm 104.3 and gives
  the Goldreich–Levin bridge [PS10, §3.10].
* `OracleSecurity` gives the fixed-length scheme, codecs and oracle games [PS10, §7.1.4].
  The proof of `TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.padded_cpa` is pending.
* `AdaptiveSecurity` gives the multi-challenge game and its cap-one correspondence.
* `AdaptiveCPA` lifts single-challenge CPA security to the adaptive game (stated).
* `BitwiseCPA` gives CPA and adaptive CPA security of the padded bitwise scheme (the first
  stated; the adaptive form and an existence form with `n`-bit messages follow).
* `TrapdoorCPA` specializes the oracle CPA bridge to trapdoor bit encryption.
* `NonMalleability.Indistinguishability` gives the indistinguishability-based game.
* `NonMalleability.Simulation` gives the simulation-based game and its relations.
* `Candidates.RSA` constructs `TCSlib.Cryptography.Candidates.rsaTrapdoor`.
  `TCSlib.Cryptography.Candidates.rsaTrapdoor_oneWay` uses
  `TCSlib.Cryptography.Candidates.RSAAssumption`.
* `Candidates.Rabin` constructs `TCSlib.Cryptography.Candidates.rabinBlumTrapdoor`.
  `TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_oneWay` uses
  `TCSlib.Cryptography.Candidates.FactoringAssumption` and `TCSlib.Cryptography.Candidates.BlumDensity`.
* `Candidates.DDH` defines the reusable safe-prime DDH assumption.
* `ElGamal` gives the group-message scheme `TCSlib.Cryptography.Candidates.elGamal`.
  `TCSlib.Cryptography.Candidates.elGamal_correct` handles admissible messages.
  `TCSlib.Cryptography.Candidates.elGamal_secure` uses
  `TCSlib.Cryptography.Candidates.DDHAssumption` for `TCSlib.Cryptography.Candidates.egGroupGen`
  and a negligible full-length exception bound for the safe-prime generator.
* `Regev` proves finite subset-sum encryption correctness and an explicit DLWE security bound
  with a leftover-hash error [Pei16, §5.2.1].

The three candidate routes take arithmetic efficiency as
`TCSlib.Cryptography.Candidates.ArithmeticFP`. RSA and Rabin share the trapdoor-bit route.
Its Goldreich–Levin bridge `TCSlib.Cryptography.TrapdoorCollection.OneWay.exists_glPad_singleBitSecure`
requires the encoding-width premise `henc`. ElGamal uses its own group-message game.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016.
-/

## ===== TCSlib/Cryptography/Encryption/PublicKey/AdaptiveSecurity.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Adaptive left-or-right public-key security

An extension of the fixed-length game of [PS10, Definition 171.5] with one hidden bit,
one generated key pair, and a polynomial cap on fresh challenges. The adversary may
choose each pair of messages after seeing the earlier answers. In the CCA2 game the
decryptor refuses every ciphertext already issued as a challenge.

## Main definitions

* `FixedLengthPKScheme.adaptiveIndImpl` implements the two oracles and their history.
* `FixedLengthPKScheme.adaptiveIndGame` runs the existing adversary codec with those oracles.
* `FixedLengthPKScheme.AdaptiveINDSecure` is the negligible-advantage condition.

## Main results

* `FixedLengthPKScheme.adaptiveIndGame_one` recovers the exact single-challenge game.
* `FixedLengthPKScheme.AdaptiveINDSecure.single` specializes the security predicate.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
-/

namespace TCSlib.Cryptography.Composability.FixedLengthPKScheme

open Complexity Turing TCSlib.Cryptography.Games

variable (S : FixedLengthPKScheme)

/-- Extend [PS10, Definition 171.5] to a bounded list of fresh left-or-right challenges.
The history records each issued challenge. A decryption query in the history receives
the existing refusal reply. Once the challenge cap is reached the game repeats the
latest ciphertext, with a zero reply for a zero cap and empty history. The history is
a list so a repeated ciphertext still consumes one fresh challenge. -/
noncomputable def adaptiveIndImpl (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (cap : ℕ) : QueryImpl (S.indSpec n) (List (Fin (S.ctLen.eval n) → Bool)) unifSpec
  | 0, c, history =>
    if cast (S.indSpec_decDom n) c ∈ history then
      .pure (zeroBits _, history)
    else
      (S.indImpl atk b n pk sk 0 c history.head?).bind fun res => .pure (res.1, history)
  | 1, mm, history =>
    if history.length < cap then
      (S.indImpl atk b n pk sk 1 mm none).bind fun res => .pure (res.1, res.2.toList ++ history)
    else
      match history.head? with
      | none => .pure (zeroBits _, history)
      | some c =>
        (S.indImpl atk b n pk sk 1 mm (some c)).bind fun res => .pure (res.1, history)

/-- Decryption refuses every ciphertext recorded in the challenge history. -/
theorem adaptiveIndImpl_dec_issued (atk : Attack) (b : Bool) (n : ℕ)
    (pk sk : List Bool) (cap : ℕ) (c : (S.indSpec n).dom 0)
    (history : List (Fin (S.ctLen.eval n) → Bool))
    (hc : cast (S.indSpec_decDom n) c ∈ history) :
    S.adaptiveIndImpl atk b n pk sk cap 0 c history = .pure (zeroBits _, history) := by
  rw [adaptiveIndImpl, if_pos hc]

/-- A challenge below the cap uses the single game's fresh challenge branch, then
adds that ciphertext to the history. -/
theorem adaptiveIndImpl_challenge_fresh (atk : Attack) (b : Bool) (n : ℕ)
    (pk sk : List Bool) (cap : ℕ) (mm : (S.indSpec n).dom 1)
    (history : List (Fin (S.ctLen.eval n) → Bool)) (h : history.length < cap) :
    S.adaptiveIndImpl atk b n pk sk cap 1 mm history =
      (S.indImpl atk b n pk sk 1 mm none).bind
        (fun res => .pure (res.1, res.2.toList ++ history)) := by
  rw [adaptiveIndImpl, if_pos h]

/-- A fresh challenge samples an encryption tape, returns the selected encryption, and
prepends exactly that ciphertext to the history.

**Proof sketch.** Read the original game's first-challenge equation on the specification's
type, then simplify the continuation that saves the returned ciphertext. -/
theorem adaptiveIndImpl_challenge_encrypt (atk : Attack) (b : Bool) (n : ℕ)
    (pk sk : List Bool) (cap : ℕ) (mm : (S.indSpec n).dom 1)
    (history : List (Fin (S.ctLen.eval n) → Bool)) (h : history.length < cap) :
    S.adaptiveIndImpl atk b n pk sk cap 1 mm history =
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let halves := FixedLengthScheme.splitHalf (cast (S.indSpec_challengeDom n) mm)
        let c := padFin (S.ctLen.eval n) (S.enc.runAt n
          (pairEncode pk (List.ofFn (if b then halves.2 else halves.1))) r)
        .pure (cast (S.indSpec_challengeRng n).symm c, c :: history) := by
  rw [S.adaptiveIndImpl_challenge_fresh atk b n pk sk cap mm history h,
    S.indImpl_challenge_none_onSpec, OracleComp.bind_assoc]
  simp only [OracleComp.pure_bind, Option.toList_some, List.singleton_append]

/-- A positive cap of one issues a fresh first challenge, as in Definition 171.5. -/
private theorem adaptiveIndImpl_one_empty (atk : Attack) (b : Bool) (n : ℕ)
    (pk sk : List Bool) (mm : (S.indSpec n).dom 1) :
    S.adaptiveIndImpl atk b n pk sk 1 1 mm [] =
      (S.indImpl atk b n pk sk 1 mm none).bind (fun res => .pure (res.1, res.2.toList)) := by
  rw [S.adaptiveIndImpl_challenge_fresh atk b n pk sk 1 mm []
    (by simp only [List.length_nil, Nat.zero_lt_one])]
  simp only [List.append_nil]

/-- At a full challenge cap, repeat the latest ciphertext without adding to the history. -/
theorem adaptiveIndImpl_challenge_full (atk : Attack) (b : Bool) (n : ℕ)
    (pk sk : List Bool) (cap : ℕ) (mm : (S.indSpec n).dom 1)
    (history : List (Fin (S.ctLen.eval n) → Bool)) (h : cap ≤ history.length)
    (c : Fin (S.ctLen.eval n) → Bool) (hc : history.head? = some c) :
    S.adaptiveIndImpl atk b n pk sk cap 1 mm history =
      (S.indImpl atk b n pk sk 1 mm (some c)).bind
        (fun res => .pure (res.1, history)) := by
  rw [adaptiveIndImpl, if_neg (Nat.not_lt_of_ge h), hc]

/-- A zero challenge cap keeps the initial history empty and returns the zero reply. -/
theorem adaptiveIndImpl_challenge_zero (atk : Attack) (b : Bool) (n : ℕ)
    (pk sk : List Bool) (mm : (S.indSpec n).dom 1) :
    S.adaptiveIndImpl atk b n pk sk 0 1 mm [] = .pure (zeroBits _, []) := by
  rw [adaptiveIndImpl, if_neg (Nat.not_lt_zero _)]
  rfl

/-- Decryption outside the history uses the original oracle's availability and decoding
rules. Its answer leaves the full history unchanged. -/
theorem adaptiveIndImpl_dec_other (atk : Attack) (b : Bool) (n : ℕ)
    (pk sk : List Bool) (cap : ℕ) (c : (S.indSpec n).dom 0)
    (history : List (Fin (S.ctLen.eval n) → Bool))
    (hc : cast (S.indSpec_decDom n) c ∉ history) :
    S.adaptiveIndImpl atk b n pk sk cap 0 c history =
      (S.indImpl atk b n pk sk 0 c history.head?).bind (fun res => .pure (res.1, history)) := by
  rw [adaptiveIndImpl, if_neg hc]

/-- At cap one, each oracle call agrees with the old game when the optional challenge is
represented as a list.

**Proof sketch.** Split by oracle and old challenge state. For decryption the
single-game state is preserved. A fresh challenge creates one list entry, and a repeat
returns the same state. -/
theorem adaptiveIndImpl_one (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (i : Fin 2) (x : (S.indSpec n).dom i) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.adaptiveIndImpl atk b n pk sk 1 i x s.toList =
      (S.indImpl atk b n pk sk i x s).bind (fun res => .pure (res.1, res.2.toList)) := by
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> decide
  rcases hi with rfl | rfl
  · cases s with
    | none =>
      rw [Option.toList_none, S.adaptiveIndImpl_dec_other atk b n pk sk 1 x []
        List.not_mem_nil, List.head?_nil, S.indImpl_dec_onSpec]
      split <;> simp only [OracleComp.pure_bind, Option.toList_none]
    | some c =>
      by_cases h : cast (S.indSpec_decDom n) x = c
      · rw [S.adaptiveIndImpl_dec_issued atk b n pk sk 1 x (some c).toList (by
          simp only [Option.toList_some, List.mem_singleton]; exact h)]
        rw [S.indImpl_dec_onSpec, h]
        simp
      · rw [S.adaptiveIndImpl_dec_other atk b n pk sk 1 x (some c).toList (by
          simp only [Option.toList_some, List.mem_singleton]; exact h)]
        simp only [Option.toList_some, List.head?_cons, S.indImpl_dec_onSpec]
        split <;> simp only [OracleComp.pure_bind, Option.toList_some]
  · cases s with
    | none => exact S.adaptiveIndImpl_one_empty atk b n pk sk x
    | some c =>
      rw [S.adaptiveIndImpl_challenge_full atk b n pk sk 1 x (some c).toList (by simp) c (by simp),
        S.indImpl_challenge_repeat_onSpec]
      simp only [OracleComp.pure_bind]

/-- Cap-one simulation is the single-challenge simulation with its final state encoded
as a list.

**Proof sketch.** Induct over the adversary's query tree and apply the per-call equality. -/
theorem simulate_adaptiveIndImpl_one (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    {α : Type} (t : OracleComp (S.indSpec n) α) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    simulate (S.adaptiveIndImpl atk b n pk sk 1) t s.toList =
      (simulate (S.indImpl atk b n pk sk) t s).bind
        (fun res => .pure (res.1, res.2.toList)) := by
  induction t generalizing s with
  | pure a => simp only [simulate_pure, OracleComp.pure_bind]
  | query i x k ih =>
    simp only [simulate_query, S.adaptiveIndImpl_one, OracleComp.bind_assoc, OracleComp.pure_bind]
    congr 1
    funext res
    exact ih res.1 res.2

/-- The left-or-right game uses one key and hidden bit across the adaptive queries. -/
noncomputable def adaptiveIndGame (atk : Attack) (A : NUPPT) (q cap : ℕ) (b : Bool) (n : ℕ) :
    ProbComp Bool :=
  (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (A.Coins n)).bind fun r =>
  (simulate (S.adaptiveIndImpl atk b n (pairFstD (S.gen.runAt n [] rg))
      (pairSndD (S.gen.runAt n [] rg)) cap)
      (A.toCompOn (S.indCodec n) n q (pairFstD (S.gen.runAt n [] rg)) r) []).bind
    fun res => .pure (res.1 0)

/-- The experiment's only sampled keys come from one activation of key generation. -/
theorem adaptiveIndGame_eq (atk : Attack) (A : NUPPT) (q cap : ℕ) (b : Bool) (n : ℕ) :
    S.adaptiveIndGame atk A q cap b n =
      (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
      (ProbComp.sample (A.Coins n)).bind fun r =>
      (simulate (S.adaptiveIndImpl atk b n (pairFstD (S.gen.runAt n [] rg))
          (pairSndD (S.gen.runAt n [] rg)) cap)
          (A.toCompOn (S.indCodec n) n q (pairFstD (S.gen.runAt n [] rg)) r) []).bind
        fun res => .pure (res.1 0) := rfl

/-- The cap-one experiment and the existing single-challenge experiment return the same bit
on the same sampled generator and adversary tapes.

**Proof sketch.** Fix both sampled tapes and apply the simulation correspondence.
Both experiments read the same bit of the simulation's result. -/
theorem adaptiveIndGame_one (atk : Attack) (A : NUPPT) (q : ℕ) (b : Bool) (n : ℕ) :
    S.adaptiveIndGame atk A q 1 b n = S.indGame atk A q b n := by
  simp only [S.adaptiveIndGame_eq, S.indGame_eq]
  congr 1
  funext rg
  congr 1
  funext r
  rw [← Option.toList_none (α := Fin (S.ctLen.eval n) → Bool), S.simulate_adaptiveIndImpl_one,
    OracleComp.bind_assoc]
  simp only [OracleComp.pure_bind]

/-- The adversary's left-or-right advantage is negligible for polynomial total and
challenge budgets. The first catalog witnesses will have message length equal to the
security parameter. -/
def AdaptiveINDSecure (atk : Attack) : Prop :=
  ∀ (A : NUPPT) (q cap : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
    advantage (S.adaptiveIndGame atk A (q.eval n) (cap.eval n) false n)
      (S.adaptiveIndGame atk A (q.eval n) (cap.eval n) true n) ≤ ε n

/-- The adaptive predicate quantifies over both the total query and challenge budgets. -/
theorem adaptiveINDSecure_iff (atk : Attack) :
    S.AdaptiveINDSecure atk ↔
      ∀ (A : NUPPT) (q cap : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
        advantage (S.adaptiveIndGame atk A (q.eval n) (cap.eval n) false n)
          (S.adaptiveIndGame atk A (q.eval n) (cap.eval n) true n) ≤ ε n :=
  Iff.rfl

/-- Adaptive security entails security in the original game.

**Proof sketch.** Use the constant cap one and the exact simulation equation. -/
theorem AdaptiveINDSecure.single {atk : Attack} (h : S.AdaptiveINDSecure atk) :
    S.INDSecure atk := by
  rw [S.adaptiveINDSecure_iff] at h
  rw [S.INDSecure_iff]
  intro A q
  obtain ⟨ε, hε, hb⟩ := h A q (.const 1)
  refine ⟨ε, hε, fun n => ?_⟩
  simpa only [PolyExpr.eval_const, S.adaptiveIndGame_one] using hb n

end TCSlib.Cryptography.Composability.FixedLengthPKScheme

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
* `BitPublicKeyScheme.SingleBitSecure.padded_cpa` (stated; a `sorry` under its sketch): single-bit
  security gives CPA security.

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

/-- **Single-bit security gives CPA security** for a padded single-bit scheme.

**Proof sketch.**
1. With CPA there is no `Dec` oracle, so the adversary's view is `pk`, its coins and the padded
   challenge `padCt L (Enc_pk(m_b))`, where its messages `m₀, m₁ ∈ {0,1}` are chosen after
   seeing `pk`.
2. If `m₀ = m₁` both games are identical. Otherwise `m_b` is `b` or `¬b`. The distinguisher `D`
   on `⟨pk, c⟩` runs `A` on `pk` (its first move gives `m₀, m₁`), answers the challenge with
   `padCt L c`, and outputs `A`'s bit, flipped when `(m₀, m₁) = (1, 0)` and replaced by `0` when
   `m₀ = m₁`.
3. Conditioning on `A`'s choice, `A`'s CPA advantage is at most `D`'s single-bit advantage
   between `⟨pk, Enc_pk(0)⟩` and `⟨pk, Enc_pk(1)⟩`, which is negligible
   (`BitPublicKeyScheme.singleBitSecure_iff`). T1 (`Games.exists_handlerMachine`) makes
   `D` a machine: `advIn` extracts `pk` from `z = ⟨pk, c⟩`, the handler answers the challenge
   with `padCt L c`, and `out` flips or zeroes the result bit as described above. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.padded_cpa
    {S : BitPublicKeyScheme} (h : S.SingleBitSecure) (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (b : Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]) re).length + 2
        ≤ L.eval n)
    (hmsg : ∀ n, 1 ≤ L.eval n) : (S.padded L hL hmsg).INDSecure .cpa := by
  sorry

end TCSlib.Cryptography.Composability

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

## ===== TCSlib/Cryptography/Games/Advantage.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Probability
import TCSlib.Cryptography.Foundations.Probability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Advantages of game-playing adversaries

Security definitions come in three shapes, each measured at one value of the security parameter:
- a **search game** (forge a tag, find a collision, invert a function): its advantage is the
  probability that the game, run with the adversary, outputs `true`;
- a **distinguishing pair** (real versus random, left versus right): its advantage is the
  difference of the two games' acceptance probabilities;
- a **guess-the-bit game**: a bit `b` is drawn, the game runs on `b`, and the adversary wins if it
  outputs `b`. Its advantage is the distance of the winning probability from `½`, which is half
  the distinguishing advantage of the two games (`guessAdv_eq_half_advantage`).

Games are `ProbComp Bool`s built from the adversary; these shapes are what asymptotic security
definitions wrap with "negligible for every efficient adversary".

## Main definitions

* `Games.accept G`: the probability that `G` outputs `true`.
* `Games.advantage G₀ G₁`: `|Pr[G₀ = 1] − Pr[G₁ = 1]|`.
* `Games.guessGame G`, `Games.guessAdv G`: the guess-the-bit game over `G : Bool → ProbComp Bool`
  and its advantage `|Pr[win] − ½|`.

## Main results

* `advantage_triangle`, `advantage_hybrid`, `exists_advantage_hybrid_gap`: the hybrid argument;
  the advantage between the ends of a chain of games is at most the sum of the advantages between
  neighbours, so some neighbouring pair carries a `1/n` share of it, for `n` hops
  ([PS10, Lemma 71.6]).
* `guessAdv_eq_half_advantage`: the guess-the-bit advantage is half the distinguishing advantage
  between the games for `b = 1` and `b = 0` (the identity behind [PS10, Lemma 73.8]).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §3.1 (Def 69.4, computational indistinguishability), Lemma 71.6 (the hybrid lemma), Lemma 73.8
  (the prediction lemma) and Definition 168.1 (the experiments `IND_b` for a fixed challenge bit).
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
-/

namespace TCSlib.Cryptography.Games

open Finset ProbComp

/-- The probability that the game `G` outputs `true`. -/
noncomputable def accept (G : ProbComp Bool) : ℝ := prob G (· = true)

/-- The acceptance probability is the probability of the output `true`:
`accept G = prob G (· = true)`. -/
theorem accept_eq (G : ProbComp Bool) : accept G = prob G (· = true) :=
  rfl

/-- The **distinguishing advantage** between two games: `|Pr[G₀ = 1] − Pr[G₁ = 1]|`.
[PS10, §3.1] -/
noncomputable def advantage (G₀ G₁ : ProbComp Bool) : ℝ := |accept G₀ - accept G₁|

/-- The distinguishing advantage is the absolute gap of the acceptance probabilities:
`advantage G₀ G₁ = |accept G₀ - accept G₁|`. -/
theorem advantage_eq (G₀ G₁ : ProbComp Bool) : advantage G₀ G₁ = |accept G₀ - accept G₁| :=
  rfl

/-- An acceptance probability is nonnegative. -/
theorem accept_nonneg (G : ProbComp Bool) : 0 ≤ accept G := prob_nonneg G _

/-- An acceptance probability is at most one. -/
theorem accept_le_one (G : ProbComp Bool) : accept G ≤ 1 := prob_le_one G _

/-- The distinguishing advantage is nonnegative. -/
theorem advantage_nonneg (G₀ G₁ : ProbComp Bool) : 0 ≤ advantage G₀ G₁ := abs_nonneg _

/-- The distinguishing advantage is symmetric. -/
theorem advantage_comm (G₀ G₁ : ProbComp Bool) : advantage G₀ G₁ = advantage G₁ G₀ :=
  abs_sub_comm _ _

/-- A game has no advantage against itself. -/
@[simp] theorem advantage_self (G : ProbComp Bool) : advantage G G = 0 := by simp [advantage]

/-- The distinguishing advantage is at most one. -/
theorem advantage_le_one (G₀ G₁ : ProbComp Bool) : advantage G₀ G₁ ≤ 1 := by
  unfold advantage
  rw [abs_le]
  constructor <;> linarith [accept_nonneg G₀, accept_nonneg G₁, accept_le_one G₀, accept_le_one G₁]

/-- **One game hop:** the advantage between `G₀` and `G₂` is at most the sum of the advantages
through `G₁`. -/
theorem advantage_triangle (G₀ G₁ G₂ : ProbComp Bool) :
    advantage G₀ G₂ ≤ advantage G₀ G₁ + advantage G₁ G₂ :=
  abs_sub_le _ _ _

/-- **The hybrid argument:** along a chain of games `G 0, …, G n`, the advantage between the ends
is at most the sum of the advantages between neighbours: the telescoping inequality in the proof of
[PS10, Lemma 71.6]. It is the concrete layer's `abs_sub_le_sum_hybrids` for the acceptance
probabilities. -/
theorem advantage_hybrid (G : ℕ → ProbComp Bool) (n : ℕ) :
    advantage (G 0) (G n) ≤ ∑ i ∈ range n, advantage (G i) (G (i + 1)) :=
  abs_sub_le_sum_hybrids (fun i => accept (G i)) n

/-- **The hybrid lemma:** along a chain `G 0, …, G n` of `n > 0` hops (`n + 1` games), some
neighbouring pair has advantage at least `advantage (G 0) (G n) / n`. [PS10, Lemma 71.6]

**Deviation:** sharper than the source, which takes `m` distributions (`m − 1` hops), a threshold
`ε < |g₁ − g_m|`, and concludes `> ε/m`. Here the divisor is the number of hops and the bound is
the exact endpoint advantage; the source's form follows with `m = n + 1`. It is the concrete
layer's `exists_hybrid_gap` for the acceptance probabilities. -/
theorem exists_advantage_hybrid_gap (G : ℕ → ProbComp Bool) {n : ℕ} (hn : 0 < n) :
    ∃ i < n, advantage (G 0) (G n) / n ≤ advantage (G i) (G (i + 1)) :=
  exists_hybrid_gap (fun i => accept (G i)) hn

/-! ### Guess-the-bit games -/

/-- The **guess-the-bit game** over `G`: draw a uniform bit `b`, run `G b`, and win if its output
is `b`: the prediction experiment `b ← {0,1}; t ← X^b : A(t) = b` of [PS10, Lemma 73.8], with
`G b` the whole game for challenge bit `b`. -/
noncomputable def guessGame (G : Bool → ProbComp Bool) : ProbComp Bool :=
  (sample Bool).bind fun b => (G b).bind fun b' => .pure (decide (b' = b))

/-- The guess-the-bit game samples `b`, runs `G b` and outputs whether it returned `b`:
`guessGame G = (sample Bool).bind fun b => (G b).bind fun b' => .pure (decide (b' = b))`. -/
theorem guessGame_eq (G : Bool → ProbComp Bool) :
    guessGame G = (sample Bool).bind fun b => (G b).bind fun b' => .pure (decide (b' = b)) :=
  rfl

/-- The **guess-the-bit advantage**: how far the winning probability is from `½`. -/
noncomputable def guessAdv (G : Bool → ProbComp Bool) : ℝ := |accept (guessGame G) - 1 / 2|

/-- The winning probability of the guess-the-bit game is the average of `Pr[G 1 = 1]` and
`Pr[G 0 = 0]`. [PS10, proof of Lemma 73.8]

**Proof sketch.** Total probability over the uniform bit (two equally likely values), and
`Pr[G 0 = 0] = 1 − Pr[G 0 = 1]`. -/
theorem accept_guessGame (G : Bool → ProbComp Bool) :
    accept (guessGame G) = (accept (G true) + (1 - accept (G false))) / 2 := by
  classical
  have hnot : prob (G false) (· = false) = 1 - accept (G false) := by
    rw [accept, ← prob_not]
    exact prob_congr _ fun b => by cases b <;> simp
  unfold accept guessGame
  rw [prob_bind, expect_sample]
  simp only [Fintype.univ_bool, mem_singleton, Bool.true_eq_false, not_false_eq_true,
    sum_insert, sum_singleton, Fintype.card_bool, prob_bind]
  have h1 : expect (G true) (fun b' => prob (OracleComp.pure (decide (b' = true))) (· = true)) =
      prob (G true) (· = true) := by
    rw [prob_eq_expect]; congr 1; funext b'; cases b' <;> simp [prob_pure]
  have h0 : expect (G false) (fun b' => prob (OracleComp.pure (decide (b' = false))) (· = true)) =
      prob (G false) (· = false) := by
    rw [prob_eq_expect]; congr 1; funext b'; cases b' <;> simp [prob_pure]
  rw [h1, h0, hnot]
  simp only [accept]
  push_cast
  ring

/-- **Guessing versus distinguishing:** `|Pr[win] − ½| = |Pr[G 1 = 1] − Pr[G 0 = 1]| / 2`. This
is the identity behind [PS10, §3.1.1, Lemma 73.8]: a predictor with success `½ + δ` is a
distinguisher with advantage `2δ`, and conversely.

**Deviation:** stated exactly, at one value of the security parameter, for whole games; the
absolute value replaces the source's "without loss of generality" complement of the distinguisher.
[PS10, Def 168.1] is stated in the distinguishing form only, with its experiments `IND_0`, `IND_1`
as the games `G false`, `G true`. The concrete layer's counterpart is `predict_eq`
(`TCSlib.Cryptography.Asymptotic.Ensembles`). -/
theorem guessAdv_eq_half_advantage (G : Bool → ProbComp Bool) :
    guessAdv G = advantage (G true) (G false) / 2 := by
  unfold guessAdv advantage
  rw [accept_guessGame]
  rw [show (accept (G true) + (1 - accept (G false))) / 2 - 1 / 2 =
      (accept (G true) - accept (G false)) / 2 by ring, abs_div, abs_two]

end TCSlib.Cryptography.Games
