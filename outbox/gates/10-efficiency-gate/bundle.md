## ===== briefs/pass-shelat-ch5-8/gates/10-efficiency/pack.md =====

# Gate 10 · shared reduction-machine efficiency

Round 1. Auditor Codex. Draft [PR #285](https://github.com/Shilun-Allan-Li/tcslib/pull/285)
at 747cc18ddb53979919d107fefed450191eb31743, targeting cryptography/pass-shelat-ch2-4 on base e226b470e25cb08a9fe8b10f9f5dd54fc55c1808.

This proof audit covers the four formerly admitted statements in
Games/Efficiency and their six helper modules. The theorem statements passed
Gate 04. The source is [PS10], R. Pass and a. shelat, A Course in Cryptography,
third edition, January 2010, §2.1 and the reduction-machine uses of the later
security proofs. The attached design explains the exact machine contracts.

## Plain handler and input-free companion

Check that exists_handlerMachine constructs a non-uniform polynomial-time
machine for the simulated handler, with arbitrary initial state carried in
polynomial-length advice and the exact seed/adversary coin bijection.
Review the actual activation loop and its length bound. Test the reasoning
at zero query budget, malformed moves, wrong-width payloads and zero-width
payloads. The componentwise default of PolyHandler.answer is part of the
frozen statement. Confirm that the argument covers every adversary and
handler coin tape.

For exists_toCompOn_of_toComp, check the preserved coin polynomial and the
run equation after the input is discarded. The conclusion is quantified over
every codec, oracle specification, output type, budget and actual input.

## Interactive handler

Independently derive the query bound q·perCall + finCall and activation
allowance q·(perCall+2) + finCall + 2. Review the replay invariant and its
adversary, call and finalization phases. Check every outer answer, including
answers inconsistent with earlier replies. The raw machine must preserve the
answer supplied by the outer tree. Check pending queries at budget zero,
all terminal paths, and the combined answer/state default. Confirm that the
cost bound is established before reconstructing the tree from replay.

## Oracle-model bridge

For exists_toOracleAdversary_of_bitCodec, verify the history translation,
the preserved order and coins, and equality on every machine output word.
Review the timeout, false/true verdicts, malformed payloads, and the case
where the single oracle's domain has width zero. Check that the equality
covers all budgets and deterministic oracle functions.

## Proof and interface review

Inspect the seven source files and exact diff, the issued brief, design,
worker report and maintainer verification. Check the four frozen headers,
all older declarations, the eleven added total reader lemmas, and the
published-reader discipline. Check precise imports, proof sketches and
global attributes. Examine the use of the existing GGM state-loop host and
the shared-helper requests. The disclosed wrappers and generic
generalizations were reviewed as applications of public proofs.

Seyoon approved reuse of the issue-time public provider proofs while their
inherited seal findings stay in deferred cleanup. That approval covers the
72 historical diagnostic/declaration pairs in the issued dependency record.
The new proof source is subject to the ordinary seal checks.

The verification archive includes raw native logs, the all-stored declaration
comparison, the 448-declaration axiom census, seven whole-file seals, six
controls, and the explicit-use inventory. Review the evidence against its
stated coverage and the recorded attempt dispositions.

## Findings delivery

Return gate10-efficiency-findings.md as a Markdown file in this chat.
For multiple evidence files, return a ZIP containing the Markdown and the
evidence. The user dispatches and merges.

| # | Severity | File and declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

Use blocker for a false or unusable statement or substantive scope violation,
major for a missing premise, forbidden new proof read, incomplete machine
argument or unverifiable necessary evidence, minor for documentation or API
defects, and note for further observations. Report the exact audited head and
counts by severity. The gate closes at zero blockers and zero majors.

## ===== briefs/pass-shelat-ch5-8/gates/10-efficiency/verification.md =====

# Gate 10 verification

Source 747cc18ddb53979919d107fefed450191eb31743, base e226b470e25cb08a9fe8b10f9f5dd54fc55c1808. Seven Lean sources match the pinned Git blobs.

- Ten native source checks pass, covering the six helper modules,
  Games/Efficiency, Bridges, the library root and campaign Checks. The imported
  objects are from the verified #282 tree. The 1,146 retained source inputs
  match that tree.
- All 84 older stored declarations preserve their types and metadata.
  Exactly the four intended theorem bodies differ. The source-header
  comparison is empty. All 448 declarations stored in the seven owners,
  including generated declarations, use standard Lean axioms.
- Seven whole-file seals pass. The elaborated-term collector selected all
  stored declarations and generated auxiliaries and produced 159 sealable
  foreign-definition requests. Name, owner, reducibility and instance
  metadata are checked by the existing instrumenter. Reducible exclusions
  are abbreviations, and PolyExpr.eval has its existing notation ruling.
- All six controls pass before sealing and fail at the intended six
  body-reading statements after sealing.
- The refreshed explicit inventory covers 1,031 tactic-list items and all
  five final List.cons_ne_nil argument uses. The definition heads resolve
  to their own source files. The Games style lint has zero failures or
  warnings.
- Maintainer review added eleven reader lemmas covering raw projection
  inputs, an empty polynomial family, and out-of-range length selection.
  The two affected helper files and all their consumers were checked with
  these additions.
- Review identified applications of existing proofs and generic
  generalizations in the disclosed overlap. The shared-helper requests
  remain follow-up consolidation work under the issued design.

The original 60-file Claude delivery, its manifest and reported worker head
are preserved in the [intake](../../fills/efficiency/final-r1/intake.md).
The verification archive retains the corrected telemetry and metadata
attempts and states their disposition. Source-level scope remains the four
frozen targets and their helper modules.

[Native, seal, census and scan evidence](verification.zip)
[143-module source closure at the pinned head](sources.zip)

**Ready to dispatch**

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

## ===== briefs/pass-shelat-ch5-8/fills/efficiency/issued-r1/brief.md =====

# Claude fill · shared reduction efficiency

**Issue base** `b50f0a416cbf0a9f05acf14a254ba53cd97a7701` on `cryptography/pass-shelat-ch2-4`.
**Unit** `s2b-efficiency`. **Worker** Claude. **Lean** 4.25.0 and the Mathlib revision
in that commit's `lake-manifest.json`.

Prove the four admitted theorems in `TCSlib/Cryptography/Games/Efficiency.lean`.
They turn the simulated reductions into machines quantified over by the
cryptographic assumptions. T1 is the dependency for the public-key CPA bridge.
T2, the input-free companion and T4 also support the pending private-key and
authentication proofs. The statements passed Gate 04 and landed in PR #195.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4` and start a local branch
  `fill/s2b-efficiency` at the exact issue base above. Record the base in
  `REPORT.md`. Keep the local branch at that ancestry.
- Read `policy.md`, the attached environment addendum and `README.md`.
  In `briefs/pass-shelat-ch5-8/design/S2b-efficiency.md` use the route section
  for proof design. The current paths, scope, checkpoints and commands in this
  brief supersede the historical setup notes in that design.
- Deliver every checkpoint and the final payload under
  `inbox/fills/s2b-efficiency/` on `exchange/pass-shelat-ch5-8`. Include
  `REPORT.md`, `patches/` containing the whole `git format-patch` series from the
  issue base, `src/` with owned paths, and `evidence/`. Use commit messages
  `fill s2b-efficiency: checkpoint N` and `fill s2b-efficiency: final`.
  Pull the exchange with rebase before pushing. Push only your delivery path.
  Keep the proof branch local. Campaign changes land by a maintainer PR for
  Seyoon's approval.

## Targets

| Target | Declaration in `TCSlib.Cryptography.Games` | Issue-base line |
|---|---|---:|
| T1 | `exists_handlerMachine` | 300 |
| T2 | `exists_interactiveHandlerMachine` | 510 |
| Companion | `exists_toCompOn_of_toComp` | 538 |
| T4 | `exists_toOracleAdversary_of_bitCodec` | 569 |

The source declarations are frozen. These quotes come directly from the issue base.

```lean
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
  sorry
```

```lean
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
  sorry
```

```lean
theorem exists_toCompOn_of_toComp (A : NUPPT) :
    ∃ A' : NUPPT, A'.coins = A.coins ∧ ∀ n : ℕ, ∃ φ : A.Coins n ≃ A'.Coins n,
      ∀ {ι α : Type} {spec : OracleSpec ι} (codec : MachineCodec spec α) (q : ℕ)
        (x : List Bool) (r : A.Coins n),
        A'.toCompOn codec n q x (φ r) = A.toComp codec n q r := by
  sorry
```

```lean
theorem exists_toOracleAdversary_of_bitCodec (B : NUPPT) (ℓ₁ ℓ₂ : PolyExpr) :
    ∃ B' : NUPPT, B'.coins = B.coins ∧ ∀ n : ℕ, ∃ φ : B.Coins n ≃ B'.Coins n,
      ∀ (q : ℕ) (r : B.Coins n) (f : (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)),
        (B'.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) q (φ r)).eval f =
          (B.toCompOn (bitCodec (fun _ : Fin 1 => ℓ₁.eval n) (fun _ => ℓ₂.eval n) 1) n q []
              r).evalFn (fun _ => f) 0 := by
  sorry
```

## Published interfaces

| Interface | Current provider |
|---|---|
| `NUPPT.coinLen_eq`, `runAt_eq` and machine constructors | `TCSlib/Complexity/Randomized/PPT.lean` and `NonUniform.lean` |
| `NUPPT.exists_comp`, `exists_compParam`, `exists_split`, `exists_withAdvice` and `runAtL_eq_output_layout` | `TCSlib/Complexity/Randomized/Closure.lean` |
| `decodeOracleMove_pairEncode_false`, `decodeOracleMove_pairEncode_ofFn`, `decodeOracleMove_true_two`, `decodeOracleMove_pairEncode_false_of_length_ne`, `decodeOracleMove_of_ne` | `TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/Defs.lean` |
| `decodeFin_eq_some_iff`, `decodeFin_ofFn` and `length_eq_of_decodeFin_eq_some` | `TCSlib/Cryptography/Asymptotic/Adversary.lean` |
| `GGMRed.stateLoopFun`, `stateLoopFun_poly`, `stateLoopFun_eval` and `pairEncode_append_right` | `TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Reduction.lean` |
| `StateLoop.orbit_zero`, `orbit_succ`, `gstep_iterate_eq` and `find?_range_eq_some` | `TCSlib/Complexity/Randomized/Build/StateLoop.lean` |
| `polyTimeComputable_iterateEmit` and `polyTimeComputable_iterateFind` | `TCSlib/Complexity/Randomized/Repetition.lean` |
| `decodeBitMove_query`, `decodeBitMove_ret`, `decodeBitMove_of_not_canonical` and `encodeLog_bitCodec` | `TCSlib/Cryptography/Games/BitCodec.lean` |
| `NUPPT.toComp_eq`, `toCompOn_eq`, `toCompOn_costBoundedBy` and `buildComp` case equations | `TCSlib/Cryptography/Games/Machines.lean` |
| `simulate_costBoundedBy`, `OracleComp.CostBoundedBy.bind` and the pure/query equations | `TCSlib/Cryptography/Games/Simulate.lean` and `OracleComp.lean` |
| `toComp_singleCodec`, `encodeLog_singleCodec` and `toHist` readers | `TCSlib/Cryptography/Games/Bridges/Machines.lean` |

Seyoon approved citation of the existing public helper proofs at this issue base
on 2026-11-10. The dependency screen records historical cleanup findings in
their transitive proof dependencies, including the use of `StateLoop.gstep`
inside `GGMRed.stateLoopFun_poly`. Cite the public theorems under seal in the
new proofs. Keep the cited provider files and proof bodies frozen. Record any
new missing reader in `REPORT.md` for the maintainer to triage. The existing
findings stay in the cleanup ledger.

## Proof route and checkpoints

1. **Companion.** Use `NUPPT.exists_comp` with `pre = pairSndD` and `post = id`.
   Pair projection removes the added input. Transport the coin vector along the
   equality from `coinLen_eq`, using `List.ofFn_congr` for the actual tape.
   Rewrite through `toCompOn_eq` and `toComp_eq`. Send checkpoint 1.
2. **T1.** Set up the shared canonical move/answer decoding and log appending.
   Put `List.ofFn (H.init n)` beside `A.advice n` in the advice of the new
   machine. Split coins into the handler seed and adversary tape. The bounded
   state loop retains the original input, state and log, recomputes the context,
   and advances the simulation one move at a time. Show the actual orbit fits
   the length bound, and use `GGMRed.stateLoopFun_eval` with the exact number
   of rounds. Check the zero-query case and finalization. Send checkpoint 2.
3. **T4.** Translate the ch. 2–4 history into the `Fin 1` bit-codec log, preserving
   order, then translate the move returned by `B`. Reuse the iteration and
   pairing combinators. `NUPPT.exists_compParam` exposes `1^n` to both
   translators if they need evaluated lengths. Use the published decoder cases
   and induct on the remaining budget. Check `ℓ₁(n) = 0` and the default verdict.
   Send checkpoint 3.
4. **T2.** Implement the replay of the adversary, each handler call and the
   finalization. Thread the outer-log cursor, the current inner history and the
   separate budgets. The target is equality of computation trees, including
   arbitrary outer answers. Prove the per-call and final query bounds before
   using the replay lemma. With one activation per round, the proposed replay
   bound is `(q + 1) + q * (perCall + 1) + finCall + 1` at parameter `n`.
   Include any extra initialization activation in the bound. The supplied
   cost-scaling probe exercises the pure/query induction under seal. Send
   checkpoint 4 and then the final payload.

The round-level cases in the design note include two distinct defaults.
`PolyHandler.answer` defaults componentwise. `InteractiveHandler.call`
decodes one combined word and defaults both components together. Projections
can give empty words on malformed inputs, so check canonicity by re-encoding.
At budget zero the machine still decodes a verdict, and a pending query gives
the timeout without calling its oracle. These cases apply to every replay.

## Scope and proof discipline

- Own `TCSlib/Cryptography/Games/Efficiency.lean`. Replace the four proof bodies
  and add local helpers in `TCSlib.Cryptography.Games.EffFill`. EF-1 permits helper
  modules under `TCSlib/Cryptography/Games/Efficiency/` with precise acyclic imports.
  Import the existing GGM reduction module directly from the first consumer.
  Keep helper files below 1000 lines and publish the needed reader equations and
  proof sketches. Cite public GGM loop results where they apply. New shared
  helper declarations live in the fill's namespace and the report lists them.
- EF-2 permits editing the four proof sketches to describe the proofs actually
  delivered. Preserve the statements, all existing non-target declarations
  and the statement prose in docstrings. Keep global simp attributes unchanged.
- Use published readers for other files' definitions in both tactics and term
  elaboration. `NUPPT.Coins`, `bitSpecAt`, `bitSpec`, `QueryTree` and
  `OracleAdversary` are abbreviations. For core and Mathlib use their equation
  lemmas in `simp`, `rw` and `unfold`. Preserve the policy's existing rules on
  opacity, private names, and proof axioms.
- If a frozen target appears false or a required reader has no clean route,
  give the exact failing obligation and the smallest proposed correction in
  `REPORT.md`. Continue independent targets where feasible. At a partial
  delivery identify each remaining admission and include the checked frontier.

## Checks and report

- Bootstrap from `order.txt` and the narrow `roots.txt` using the environment
  addendum. The order includes the authorized GGM reduction import. Insert any
  new helper module before its consumers and recalculate roots if imports change.
  Check one module per `scripts/lean_check_tree.sh` invocation. Keep one Lean
  process per olean tree.
- Recheck `Games/Efficiency` and `Games/Bridges` and sweep the supplied order.
  Compare the warnings with `base-sorries.txt`. A complete owner check has no
  sorry warnings. Use the checker for scratch axiom prints and probes too.
- Print the axioms of the four targets. Each completed proof should use only
  `propext`, `Classical.choice` and `Quot.sound` as needed.
- Collect foreign references from the elaborated new proofs, including
  generated matcher and projection helpers. Run an instance-aware seal of the
  touched proofs with the full candidate list, plus a control that passes
  before sealing and fails after sealing. Report the candidates, controls and
  any findings. Include the explicit-unfold scan and
  `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Games --check8b`.
- Report the issue base, each target's status, exact changed files and sketch
  edits, published helper citations, any reader or machine requests, and
  the resource, cache, bootstrap, sweep, axioms, seals and lint evidence.

**Ready to dispatch**

## ===== briefs/pass-shelat-ch5-8/design/S2b-efficiency.md =====

# S2b design note: the efficiency of reductions (the machine layer's crux)

Status: **statements restated under ruling R-04-3, at `243598b7cb0c3fdd50b22a92a011f1b77f55c8c6`
(PR #195, `Games/Efficiency.lean`); gate 04 round 2 (closing) dispatched 2026-11-05; proofs not
started.** The four targets are `sorry` under their sketches; they are the efficiency fill
(`fills/efficiency/brief-draft.md`). This note was redrafted on 2026-11-05. It replaces the note of
2026-11-04/05, whose statements (adversary without input, hidden final state, output padded with
`padFin`, no finalization, no bridge to the PRF assumption) predate R-04-3.

## The statement needed

A reduction of ch. 5–8 runs a machine adversary `A` once and answers its oracle queries with a
polynomial-time **handler**. Proved once, the targets say that the result is again a machine, so
the hardness assumptions, which quantify over machines (`Complexity.NUPPT`), apply to it. The
reduction then needs no machine construction of its own: the ch. 2–4 layer built one per reduction
(`Asymptotic/GGMReduction*`, `HardCoreGL*`, …), each several hundred lines.

### The shape of a reduction (T0, written; frozen at the fill's issue)

At parameter `n` the reduction has an input `z` and a seed `ω`, its own coins. Every function of a
handler reads them from the **context** `⟨1^n, ⟨z, ω⟩⟩`:

```lean
def seedIn (n : ℕ) (z ω : List Bool) : List Bool :=
  pairEncode (List.replicate n true) (pairEncode z ω)
```

(`seedIn_eq`). All lengths are polynomials in `n`, as `PolyExpr`s: queries and answers `din i`,
`dout i` (`bitSpecAt din dout n`, the abbreviation of `bitSpec` at the evaluated lengths), the
adversary's output `dα`, the handler's state and seed.

**`PolyHandler k din dout`** (no oracle of its own; the target spec is `unifSpec`). Fields, with
their types as in the file:

| Field | Type | Role |
|---|---|---|
| `stateLen`, `seedLen` | `PolyExpr` | lengths of the state and of the seed `ω` |
| `init` | `∀ n, Fin (stateLen.eval n) → Bool` | initial state; an arbitrary function of `n` |
| `run`, `poly` | `List Bool → List Bool`, `PolyTimeComputable run` | one query: `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨1^i, x⟩⟩⟩ ↦ ⟨y, s'⟩` |
| `advIn`, `advIn_poly` | `List Bool → List Bool`, `PolyTimeComputable advIn` | the adversary's input, from the context |
| `out`, `out_poly` | `List Bool → List Bool`, `PolyTimeComputable out` | the reduction's output, from `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, a⟩⟩` |

Derived (each with its `_eq` or case lemmas beside it): `PolyHandler.input`, `advInput`
(`H.advIn (seedIn n z (List.ofFn ω))`), `result` (`H.out` of the context, the final state and the
output), `answer` (the decoded `⟨y, s'⟩`, **componentwise** default: not a pair gives both
all-`false`, a wrong-length component is replaced by all-`false` on its own; lemmas
`answer_of_pairDecode_eq_none`, `answer_of_pairDecode_eq_some`, `answer_of_run_eq`), and `impl`,
the `QueryImpl (bitSpecAt din dout n) (Fin (H.stateLen.eval n) → Bool) unifSpec` answering with
`.pure (H.answer n z ω s i x)` (`impl_apply`).

**`InteractiveHandler k din dout k' din' dout'`** (it may query `k'` outer bit-string oracles):

| Field | Type | Role |
|---|---|---|
| `stateLen`, `seedLen` | `PolyExpr` | as above |
| `perCall` | `PolyExpr` | outer queries per inner query, at most |
| `init` | `∀ n, Fin (stateLen.eval n) → Bool` | as above |
| `run`, `poly` | `List Bool → List Bool`, `PolyTimeComputable run` | one round of a call, on `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩` (`L`: the call's outer log so far) |
| `advIn`, `advIn_poly` | `List Bool → List Bool`, `PolyTimeComputable advIn` | as above |
| `outLen` | `PolyExpr` | length of the reduction's output |
| `finCall` | `PolyExpr` | outer queries of the finalization, at most |
| `finRun`, `finRun_poly` | `List Bool → List Bool`, `PolyTimeComputable finRun` | one round of the finalization, on `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩` |

A round returns a move in `bitCodec`'s format: an outer query `⟨[false], ⟨1^j, x'⟩⟩`, or the result
`⟨[true], w⟩`. The derived definitions are `buildComp` computations over the outer oracles:

```lean
def call (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) (i : Fin k)
    (x : Fin ((din i).eval n) → Bool) :
    OracleComp (bitSpecAt din' dout' n) (Fin ((dout i).eval n + H.stateLen.eval n) → Bool) :=
  buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n) _
      (H.run (input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x)
        ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))
    (zeroBits _) (H.perCall.eval n) []
```

```lean
def finish (H : InteractiveHandler k din dout k' din' dout') (n : ℕ) (z : List Bool)
    (ω : Fin (H.seedLen.eval n) → Bool) (s : Fin (H.stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool) : OracleComp (bitSpecAt din' dout' n) (Fin (H.outLen.eval n) → Bool) :=
  buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
      (H.outLen.eval n)
      (H.finRun (finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
        ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))
    (zeroBits _) (H.finCall.eval n) []
```

`impl` runs one `call` per inner query and splits its `(dout i).eval n + H.stateLen.eval n` bits
into the answer and the new state (`Fin.castAdd`, `Fin.natAdd`). The default is **joint**
(`decodeBitMove`'s `zeroBits`): a malformed round output, a wrong total length or a spent budget
gives the all-`false` answer and state. Equation lemmas: `input_eq`, `advInput_eq`, `call_eq`,
`impl_apply`, `finInput_eq`, `finish_eq`.

### The targets

**T1** (`exists_handlerMachine`): the machine's output is exactly the finalized output of the
simulation.

```lean
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
  sorry
```

**T2** (`exists_interactiveHandlerMachine`): an oracle machine against the outer oracles, with
budget `q(n)·perCall(n) + finCall(n)`, whose computation tree is exactly the simulation followed
by the finalization.

```lean
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
  sorry
```

**The companion** (`exists_toCompOn_of_toComp`): a machine without input is a machine that
ignores its input, with the same coins, for every codec and budget.

```lean
theorem exists_toCompOn_of_toComp (A : NUPPT) :
    ∃ A' : NUPPT, A'.coins = A.coins ∧ ∀ n : ℕ, ∃ φ : A.Coins n ≃ A'.Coins n,
      ∀ {ι α : Type} {spec : OracleSpec ι} (codec : MachineCodec spec α) (q : ℕ)
        (x : List Bool) (r : A.Coins n),
        A'.toCompOn codec n q x (φ r) = A.toComp codec n q r := by
  sorry
```

**T4** (`exists_toOracleAdversary_of_bitCodec`): the bridge to the PRF assumption. A one-oracle
`bitCodec` machine with a one-bit output, on the empty input, evaluates as a ch. 2–4 next-query
machine (an equality of evaluations, not of trees: the index types are `Unit` and `Fin 1`).

```lean
theorem exists_toOracleAdversary_of_bitCodec (B : NUPPT) (ℓ₁ ℓ₂ : PolyExpr) :
    ∃ B' : NUPPT, B'.coins = B.coins ∧ ∀ n : ℕ, ∃ φ : B.Coins n ≃ B'.Coins n,
      ∀ (q : ℕ) (r : B.Coins n) (f : (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)),
        (B'.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) q (φ r)).eval f =
          (B.toCompOn (bitCodec (fun _ : Fin 1 => ℓ₁.eval n) (fun _ => ℓ₂.eval n) 1) n q []
              r).evalFn (fun _ => f) 0 := by
  sorry
```

**Who consumes them** (`gates/04-s2b/resolutions-r1.md`, the table of the eight prong sketches):
T1 for Lamport (Thm 137.2), hash-and-sign's `B` (Thm 144.1) and `padded_cpa`; T2 for hash-and-sign's
`C`, the PRF MAC (Thm 135.4), the CPA/CCA1 scheme (Thm 168.2), CCA2 (Thm 170.4) and
non-malleability (Thm 175.9 ⇒); T4 with T2 for the three PRF-based ones; the companion wherever the
adversary has no input. Two consumer-side notes:
- **T4 after T2.** T2's machine runs on the input `z` with codec index `H.outLen.eval n`; T4 needs
  the empty input, one outer oracle with `din' = fun _ => ℓ₁` and `dout' = fun _ => ℓ₂`, and the
  literal output length `1`. A consumer hard-wires `z` (`NUPPT.exists_withAdvice`, then
  `NUPPT.exists_comp` to re-pair the input) and rewrites `H.outLen.eval n = 1` with
  `PolyExpr.eval_const`. That glue is the prongs', not the fill's.
- **Time in `n + |z|`.** `B`'s running time is polynomial in its whole input, so in `n + |z|`. A
  reduction that claims time polynomial in `n` alone bounds `|z|` itself.

## A close relative (found 2026-11-05)

Frederick's GGM reduction machine (`TCSlib/Cryptography/Asymptotic/GGMReduction.lean`,
`GGMReductionEval.lean`) is T1's construction for one handler, a lazily sampled table:
- it runs a next-query machine to completion in a state loop, holding the encoded history and the
  table; each round runs the machine, decodes the move and answers from the reduction's own coins;
- its loop, `GGMRed.stateLoopFun` with `stateLoopFun_poly` and `stateLoopFun_eval`, is generic in
  start, step, acceptance and output, and **is reused verbatim** (by citation);
- the round, `rawFun_poly` and the GGM identity are specific, and are generalized by analogy.

The fill adds the **log-replay variant** (T2) for reductions that are oracle machines. GGM becomes
an instance of T1 at the integration of ch. 2–4 (coordination point F-4). That is not a target of
this fill: the T3 of earlier drafts is gone from the file, and the near-duplication of GGM's round
goes in the duplication ledger at the fill's landing, until F-4.

## Relation to P^O = P (checked 2026-11-05, at the user's prompt)

In substance the efficiency result is *FP with an efficiently implementable oracle is FP*. The
Turing-machine form is `Turing.FinOracleTM.exists_plain_simulation`
(`Complexity/TuringMachine/Build/OracleSim.lean`), behind `Complexity.POracle_eq_P_of_mem_P`
(`ClassOracle/Classes.lean`). Both are now on this branch (`main` was merged, #186). They are
**not reused**:
1. **The machine model.** They are about oracle Turing machines ([AB09, Def 3.4]: query tape,
   `qQuery`/`qYes`/`qNo`). Our adversaries are plain machines restarted on the encoded history
   (D7). In that model the statement is function-level: closure of polynomial-time functions under
   polynomially bounded iteration (`Complexity.polyTimeComputable_iterateFind`, through
   `GGMRed.stateLoopFun`).
2. **The oracles.** They need a *language* oracle decided by a plain machine (one-bit answers, no
   state, no coins). Our handlers answer strings, keep state and read a seed.

Routing through them would need a bridge from `NUPPT` next-move machines to oracle Turing
machines, which costs more than the function-level route.

## The route

Common to every proof: the machine is `NUPPT.ofPolyTime` of a polynomial-time function of the raw
layout `⟨⟨⟨1^n, y⟩, α⟩, r⟩`, read only through `runAtL_eq_output_layout`, `output_ofPolyTime`,
`advice_ofPolyTime`, `coins_ofPolyTime` and the projections `inParam_layout`, `inArg_layout`,
`inAdvice_layout`, `inCoins_layout` (`Complexity/Randomized/Closure.lean`, `PPT.lean`), or it comes
from a closure theorem (`NUPPT.exists_comp`, `exists_split`). Polynomial time is
`GGMRed.stateLoopFun_poly` on a round built from the pairing calculus, `polyTimeComputable_ite`,
`polyTimeComputable_unaryPoly` (to write `1^{p(n)}` from `1^n`) and
`NUPPT.polyTimeComputable_output`.

### Shared pieces

- **S1. The string layer of `bitCodec`.**
  - *Appending to a log is concatenation:* `(bitCodec …).encodeLog (h ++ [e]) = encodeLog h ++
    pairEncode (encodeEntry e) []`, by induction from `MachineCodec.encodeLog_nil`/`_cons` and
    `GGMRed.pairEncode_append_right` (the pattern of `GGMRed.histEnc_append_single`). With
    `encodeLog_bitCodec` the output length of the codec does not matter.
  - *A polynomial-time canonical decoder* that agrees with `decodeBitMove` on **every** word:
    canonical query word, canonical output word, or the default. It is read through
    `decodeBitMove_query`, `decodeBitMove_ret`, `decodeBitMove_eq_query_iff` and
    `decodeBitMove_of_not_canonical`, and `decodeIdx_eq_some_iff`/`_eq_none_iff` for the index.
    Canonicity is tested by **re-encoding and comparing** (`polyTimeComputable_pairEq`), never by
    projections alone: `pairFstD`/`pairSndD` return `[]` on a malformed word, and when `din i (n)`
    or `dα(n)` is `0` an empty payload is valid. The payload length `(din i).eval n` is selected
    by a `k`-way case split on the decoded index (`k` is fixed), by induction on `k` with
    `polyTimeComputable_ite`.
  - *Fixed-length decoding with a default* (`(decodeFin ℓ w).getD (zeroBits ℓ)` as a string
    function), read through `decodeFin_ofFn`, `length_eq_of_decodeFin_eq_some` and
    `GGMRed.decodeFin_eq_some_iff`; and splitting a `dout + stateLen` word.
- **S2. Machine glue.**
  - **The initial state goes into the advice.** `init` is an arbitrary function of `n`, not a
    polynomial-time one. The machine takes `⟨A.advice n, List.ofFn (H.init n)⟩` as its advice
    (`combineAdvice` or a pair, length bound from `advice_length` and `stateLen`). So `B` is
    non-uniform even when `A` is uniform. T1 and T2 do not claim uniformity, and the assumptions
    quantify over non-uniform machines. Neither Lean sketch says this yet.
  - **Coins.** `NUPPT.exists_split` with `p = H.seedLen` turns `B₀` (argument `⟨y, ω⟩`, coins `r`,
    with `B₀.coins = A.coins`) into `B` with `B.coins = .add H.seedLen A.coins`. `φ` is
    `Fin.appendEquiv` composed with the transport along `B.coinLen n = H.seedLen.eval n +
    A.coinLen n`. That equation needs `NUPPT.coinLen_eq` (prerequisite 1, below) and
    `PolyExpr.eval_add`. Then `List.ofFn (φ (ω, r)) = List.ofFn ω ++ List.ofFn r`
    (`List.ofFn_fin_append`, `List.ofFn_congr`), and `take`/`drop` give `ω` and `r`. This is the
    pattern of `exists_queryChain_nuppt` (`Asymptotic/MultiMessageLemmas.lean`).
- **S3. A replay lemma for `buildComp`.** Say that a next-move function `next` *replays* a tree
  `t` from a log `O` when `next O` is `t`'s first move and, at a query node, `next` replays every
  continuation from `O` extended by that query and its answer. If `next` replays `t` from `O`, and
  `t` is `CostBoundedBy (fun _ => 1)` within `b`, then `buildComp next timeout b O = t`. The proof
  is an induction on `t` with `buildComp`'s four case lemmas. T2 uses it. (T4 compares two
  different specs, so it needs its own induction.) It is a private helper, requested for promotion
  in the report.

### T1 (`exists_handlerMachine`): simulation inside a plain machine

1. **The loop.** `B₀`'s raw function is `GGMRed.stateLoopFun start step acc out R Bd` on the layout
   `x = ⟨⟨⟨1^n, ⟨z, ω⟩⟩, α⟩, r⟩`. The state holds only fixed-length data: `A`'s encoded inner log
   (at most `q(n)` entries `⟨1^i, ⟨x, y⟩⟩`), `H`'s state (`stateLen(n)` bits), a unary query
   counter, and on stopping `A`'s output and a done flag. The context `seedIn n z ω` and `A`'s
   input `H.advIn (seedIn n z ω)` are **recomputed from `x` in every round**, so they need no
   bound. (Keeping `A`'s input in the state instead needs `PolyTimeComputable.output_length_le` on
   `H.advIn_poly`.)
2. **A round.**
   - Run `A` on `⟨A's input, encoded log⟩` with the coins `r` and `A`'s half of the advice
     (`runAtL_eq_output_layout` read backwards), and decode the move (S1).
   - On a query `(i, x)` with the counter below `q(n)`: run `H.run` on `⟨ctx, ⟨s, ⟨1^i, x⟩⟩⟩`,
     decode `⟨y, s'⟩` with `answer`'s componentwise default, append `⟨1^i, ⟨x, y⟩⟩` (S1), set the
     state to `s'` and count.
   - On a query with the counter at `q(n)`: stop with `zeroBits dα` (the codec's timeout).
   - On an output `a`: stop with `a`.
3. **Rounds.** At most `q(n) + 1`, one activation of `A` per round, so `R := q + 1`.
   `stateLoopFun_eval` needs `N ≤ R.eval |x|`, which holds because `n ≤ |x|` and
   `PolyExpr.eval_mono`.
4. **Output.** `out` returns `H.out ⟨seedIn n z ω, ⟨s, a⟩⟩`, so `B`'s output is exactly
   `H.result n z ω s a` (`result_eq`, `seedIn_eq`).
5. **The functional equation.** By induction on the remaining budget `b`: start the orbit from the
   inner log `h`, the state `s` and the counter `q(n) − b`. It stops, within `b + 1` rounds, with
   some `(a, s_fin)`, and `simulate (H.impl n z ω) (buildComp next (zeroBits _) b h) s =
   .pure (a, s_fin)` for that same pair. The ingredients are `toCompOn_eq`, `buildComp`'s case
   lemmas, `bitCodec_decodeMove`, `bitCodec_timeout`, `simulate_pure`, `simulate_query`,
   `PolyHandler.impl_apply`, `OracleComp.pure_bind` and the `answer` lemmas. Then
   `stateLoopFun_eval` and `StateLoop.orbit_succ` read off the result, and S2 transports the
   coins.

### T2 (`exists_interactiveHandlerMachine`): simulation by an oracle machine (log replay)

1. **The next-move function.** `B₀`'s argument is `⟨⟨z, O⟩, ω⟩` (`B`'s input `⟨z, O⟩`, then
   `exists_split`), where `O` is `B`'s encoded outer log. The raw function replays the whole
   reduction in a state loop. The state holds:
   - the phase (adversary, call, finalization, done);
   - `A`'s inner log and remaining budget, and `H`'s state;
   - in a call: the pending inner query `(i, x)`, the call's log `L` and its counter;
   - in the finalization: `a`, its log and its counter;
   - a cursor into `O`;
   - when done, the word to output.

   Each round performs **one activation**:
   - **adversary:** run `A`; a query within budget opens a call; an output `a`, or a query at
     budget `q(n)` (`a := zeroBits dα`), opens the finalization;
   - **call:** run `H.run` on `⟨ctx, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`, decoded with
     `decodeBitMove din' dout' ((dout i).eval n + stateLen(n))`:
     - an answer `w` (or the joint default) is split into `y` and `s'`; append `⟨1^i, ⟨x, y⟩⟩` to
       the inner log and return to the adversary;
     - an outer query with the call's budget spent gives `zeroBits`, as `buildComp` does at `0`;
     - an outer query within budget is answered from `O` at the cursor: append that entry to `L`
       and advance;
     - if `O` is exhausted, stop: **this is `B`'s next move**, the canonical query word
       (`encodeBitMove`);
   - **finalization:** the same with `H.finRun` on `⟨ctx, ⟨s, ⟨a, L⟩⟩⟩`; an output `b`, or the
     default at budget `finCall(n)`, stops with the canonical output word `⟨[true], b⟩`.
2. **The round bound.** The worker's figure **`(q + 1) + q·(perCall + 1) + finCall + 1` is
   correct**, checked against the definitions. It counts the most activations a replay can make:
   - `A.toCompOn … (q.eval n)` is `buildComp` with budget `q(n)`, so at most `q(n) + 1`
     activations of `A`, of which at most `q(n)` open a call;
   - each `call` is `buildComp` with budget `perCall(n)`, so at most `perCall(n) + 1` rounds of
     `run`;
   - `finish` is `buildComp` with budget `finCall(n)`, so at most `finCall(n) + 1` rounds of
     `finRun`.

   With one activation per round, and with the context and `A`'s input computed in `start` or
   recomputed in each round, the stopping round `N` is at most `2q + q·perCall + finCall + 2`. As a
   `PolyExpr` in `|x|`: `.add (.add (.add q (.const 1)) (.mul q (.add perCall (.const 1))))
   (.add finCall (.const 1))`. If `A`'s input is computed in a first round instead of in `start`,
   add 1. The figure is the **loop's** bound; `B`'s **query** budget is `q·perCall + finCall`.
   (The round 1 auditor's count, `q + 1` activations of `A` and `q·(perCall + 1)` of `run`,
   predates the finalization.)
3. **Polynomial size.** Every stored item has a fixed polynomial length in `n`, except the cursor
   into `O`, which is bounded by `|x|`. A per-entry bound over `Fin k` or `Fin k'` is a finite sum
   of `PolyExpr`s.
4. **The budget never binds early.** The reduction tree is `CostBoundedBy (fun _ => 1)` within
   `q·perCall + finCall`. This follows from `NUPPT.toCompOn_costBoundedBy`,
   `buildComp_costBoundedBy` for `call` and `finish`, `simulate_costBoundedBy` with cost
   `perCall(n)` per inner query, and `CostBoundedBy.bind`. Charging `perCall` per query needs a
   small scaling lemma from `CostBoundedBy (fun _ => 1) c q` to
   `CostBoundedBy (fun _ => p) c (q * p)`, which the library lacks (by induction, with
   `CostBoundedBy.mono`).
5. **The functional equation.** `B`'s decoded next move **replays** the reduction tree from the
   empty log (S3). The proof is by induction along the reduction's positions:
   - at each position, `stateLoopFun_eval` evaluates the replay on the position's outer log;
   - the reduction side unfolds through `simulate_query`, `simulate_bind`, `impl_apply`,
     `call_eq`, `finish_eq`, `OracleComp.bind_assoc`, `pure_bind` and `query_bind`;
   - `B`'s side through `toCompOn_eq`, `bitCodec_decodeMove` and `decodeBitMove_encodeBitMove`.

   S3 with step 4 gives the equality of trees. The equality is required on **every branch**, since
   the outer answers are arbitrary: the replay copies each answered entry from `O` and never
   checks it.

### The companion (`exists_toCompOn_of_toComp`)

`A' :=` `NUPPT.exists_comp A` with `pre = pairSndD` (`polyTimeComputable_pairSndD`) and
`post = id` (`polyTimeComputable_id`). Then `A'.coins = A.coins` and
`A'.runAtL n ⟨x, L⟩ r = A.runAtL n L r` (`pairSndD_pairEncode`). `φ` transports the coins along
`A.coinLen n = A'.coinLen n` (`NUPPT.coinLen_eq`, `finCongr`), so that
`List.ofFn (φ r) = List.ofFn r` (`List.ofFn_congr`). With `runAt_eq` the two next-move functions
agree on every log, and `toCompOn_eq` and `toComp_eq` conclude.

### T4 (`exists_toOracleAdversary_of_bitCodec`)

1. **`B' :=` `NUPPT.exists_comp B pre post`**, so `B'.coins = B.coins`. Neither map needs `n`: both
   decoders check the payload length `ℓ₁(n)` themselves, and they agree on it.
   - **`pre`** maps the history `⟨⟨x₁, y₁⟩, ⟨…, []⟩⟩` (`encodeHist`) to `⟨[], ⟨⟨[], ⟨x₁, y₁⟩⟩,
     ⟨…, []⟩⟩⟩`, the empty input followed by `B`'s log (`bitCodec_encodeEntry` with `1^0 = []`,
     `encodeLog_cons`, `encodeHist_cons`). It is polynomial-time as
     `Complexity.polyTimeComputable_iterateEmit` with `g = pairSndD`, emitting `⟨⟨[], e⟩, []⟩` for
     the head `e` of a non-empty suffix and nothing for `[]` (`StateLoop.isNil_poly`,
     `polyTimeComputable_ite`), with `R = var`. The emitted pieces concatenate to the nested
     encoding by `GGMRed.pairEncode_append_right`.
   - **`post`** maps a canonical query word `⟨[false], ⟨[], x⟩⟩` (tested by re-encoding) to
     `⟨[false], x⟩`, the word `⟨[true], [true]⟩` to `[true, true]`, and every other word to
     `[true, false]`. With `decodeIdx 1` accepting only `[]`, these agree with `decodeBitMove` at
     `k = 1` and `dα = 1` (`decodeBitMove_eq_query_iff`, `decodeBitMove_ret`,
     `decodeBitMove_of_not_canonical`, `decodeIdx_eq_some_iff`) and with `decodeOracleMove ℓ₁`. The
     agreement includes a payload of the wrong length, which is the verdict `false` on both sides.
     Reading `decodeOracleMove` needs its case lemmas (prerequisite 2).
2. **Evaluation.** `toOracleAdversary_eq` and `buildTree`'s case lemmas give the left side;
   `toCompOn_eq` and `buildComp`'s give the right. (Alternatively, `toComp_singleCodec` and
   `Bridge.eval_eq_evalFn` turn the left side into `OracleComp.evalFn`.) By induction on the budget,
   generalizing the corresponding histories and logs, both evaluations take the same branch: the
   answer is `f x` on both sides (`QueryTree.eval_query`, `OracleComp.evalFn_query`). At the
   timeout, `false` is bit `0` of `zeroBits 1` (`zeroBits_apply`).
3. **`φ`** transports the coins, as in the companion.

### Rule 10 map

Every proof reads other files' definitions only through published lemmas. Two are missing today and
are the fill's **prerequisites**:
1. `NUPPT.coinLen_eq`, beside `coinLen` (`Complexity/Randomized/PPT.lean`): `A.coinLen n =
   A.coins.eval n`. It is needed for every `φ`.
2. `decodeOracleMove`'s case lemmas, beside its definition (`Cryptography/Asymptotic/PRF.lean`):
   - the query word `⟨[false], x⟩` with `|x| = ℓ₁` decodes as the query;
   - with `|x| ≠ ℓ₁` it decodes as `ret false`;
   - `[true, b]` decodes as `ret b`;
   - every other word decodes as `ret false`.

   Today only the private `decodeOracleMove_eq` exists, and it is not citable (rule 11). T4 needs
   these lemmas.

Both land in the **ch. 2–4 clean-up PR** (G3-5's, after #195), before the fill is issued
(`QUEUE.md`, "G3-5 clean-up PR to-do"). The rest is published:
- the codec (`BitCodec.lean`), `buildComp`, `toComp`/`toCompOn` and `encodeLog` (`Machines.lean`);
- `simulate` (`Simulate.lean`); `bind` and `CostBoundedBy` (`OracleComp.lean`);
- `evalFn` and `eval` (`Bridges/QueryTree.lean`, `OracleAdversary.lean`);
- `toOracleAdversary`, `buildTree` and `encodeHist` (`PRF.lean`);
- the layout and closure theorems (`Closure.lean`, `PPT.lean`);
- `orbit` (`Build/StateLoop.lean`);
- `stateLoopFun` (`GGMReduction.lean`), and `decodeFin` (`Adversary.lean`, `GGMReductionEval.lean`).

`NUPPT.Coins`, `bitSpecAt`, `bitSpec`, `QueryTree` and `OracleAdversary` are abbreviations, read
through as notation.

## Obligations and size (estimate)

| Piece | Kind | Lines |
|---|---|---|
| S1: the string layer (log append, canonical decoder with the `Fin k` dispatch, fixed-length decoding, word splitting) | FP + framework | 200–350 |
| S2: machine glue (advice with `init`, `exists_split`, the coin bijection) | glue | 80–150 |
| S3: the replay lemma for `buildComp` | framework | 40–80 |
| T1: round, `start`/`acc`/`out`, polynomial time | FP | 150–250 |
| T1: orbit bound | arithmetic | 60–120 |
| T1: functional equation | framework | 150–250 |
| T2: replay round (three phases, cursor, three counters), polynomial time | FP | 250–400 |
| T2: orbit bound and round count | arithmetic | 80–150 |
| T2: cost bound (with the scaling lemma) and the replay induction | framework | 250–450 |
| The companion | glue | 30–60 |
| T4: `pre` and `post` and their polynomial time, the move correspondence, evaluation by induction | FP + framework | 150–250 |
| **Total** | | **about 1.4–2.5k** |

**Against the earlier estimates.** The old note estimated 0.8–1.5k lines, of which 150–250 were
the T0 definitions, now written, so 0.65–1.25k were proofs. The gate 04 review added 400–700 lines
for R-04-3. My breakdown of that increase agrees, at about +430–760:
- input threading, +50–100;
- exact output through `out`, +50–100;
- the finalization as a third replay phase, +150–250;
- T4, +150–250;
- the companion, +30–60.

That sum, about 1.1–2.0k, still omits three items that do not depend on R-04-3:
- the canonical decoder (S1, about +150–250). The old route assumed a handler step format of its
  own; `bitCodec`'s strict grammar came later (R-04-1);
- `init` through the advice and the coin transport (S2, about +50–100);
- T2's conclusion is an equality of trees on every branch, not of outputs, so it needs S3, the
  cost invariant and the scaling lemma (about +100–200).

Hence 1.4–2.5k. A calibration: GGM's machine (`GGMReduction.lean` 863 lines,
`GGMReductionEval.lean` 749) is one T1-like reduction.
- About 0.5–0.6k of its 1.6k lines is handler-specific: the table, the lookup loop, the tree walk
  and the concrete distinguisher's recursion.
- The rest, about 1.0k, is the part a generic T1 redoes.
- My T1 share (S1, S2, the T1 rows) is 0.64–1.12k, which is consistent.

**File size.** Efficiency.lean has 574 lines and would reach about 2–3k. `policy.md` says a file
approaching 1000 lines should be split unless there is a positive reason not to, and the campaign
lint warns above 1000 lines. Ruling below.

## Dependencies

- **Landed or in review:**
  - the S2a core (gate 02, closed): `OracleComp`, `simulate`, `QueryImpl`, `CostBoundedBy`;
  - S2b's T0, `BitCodec`, `Machines` and `Bridges` (#195; gate 04 round 2 dispatched; head
    `243598b7`);
  - the ch. 2–4 layer: `GGMRed.stateLoopFun`, `StateLoop`, `Repetition`, `Closure`, `PPT`, the
    pairing calculus, `PRF.lean`.

  Everything cited is in `Games/Efficiency.lean`'s import closure, through `Bridges/Machines` →
  `Asymptotic/PRF` → `GGMReduction`/`GGMReductionEval`.
- **Prerequisites** (ch. 2–4 clean-up PR, before issue):
  - `NUPPT.coinLen_eq`;
  - `decodeOracleMove`'s case lemmas.

  The same PR consolidates `decodeFin_eq_some_iff` (today `GGMRed.decodeFin_eq_some_iff`) and makes
  the `stateFind` family public. The fill needs neither, but the brief names their homes at issue.
- **Mathlib:** `List.ofFn_congr`, `List.ofFn_fin_append`, `Fin.appendEquiv`, `finCongr`.
- **Host rule** (`policy.md`, "Hosts come first"). The host is the shared state loop
  (`GGMRed.stateLoopFun` over `Complexity.StateLoop`). T1 and T2 are themselves the public,
  statement-gated contracts of the reduction runner. The fill's rounds are private leaf steps
  plugged into that host. S1 and S3 are candidates for the shared layer: the report requests them.

## Out of scope

- **Rewinding** the adversary: forking-lemma reductions, and simulators that rewind a verifier.
- **Several runs of the adversary**, sequential or with shared state: two-run hybrids,
  amplification by repetition. One run, once, is covered. Several runs compose at the consumer
  through `NUPPT.exists_seq`, outside these targets.
- **Variable lengths:**
  - queries, answers, outputs or states whose length depends on anything but `n`;
  - a number of oracles that depends on `n`.
- **Uniformity** of `B`: not claimed (the initial state is advice).
- **Time polynomial in `n` alone** when `|z|` is unbounded (the consumer's bound).
- **GGM as an instance** (F-4), and the consumer glue: the eight prong re-citations, and
  hard-wiring `z` before T4.

## Decisions before issue

1. **File layout** (ruling).
   - (A, recommended) The fill may add upstream helper files under `Games/Efficiency/`, imported by
     `Efficiency.lean` with one new import line. Candidates are the string layer S1 and the replay
     lemma S3, which need only `BitCodec`/`Machines`, and possibly the T2 replay round over raw
     string functions. Their public declarations carry docstrings and lemmas per policy, and are
     audited at the fill gate.
   - (B) Everything stays in `Efficiency.lean`, with a recorded justification for the 1000-line
     warning: one statement-frozen file, private helpers.
2. **Sketch edits.** Should the fill update the targets' `**Proof sketch.**` paragraphs, for example
   to add the advice for `init`, and keep the statement prose byte-identical? Recommended yes
   (`policy.md` §3, synchronization), each edit reported.

## Who and when

- **Fill item** (D-7: a Claude fill; ruled 2026-11-05), on GGM's pattern. It is issued after gate
  04 closes, #195 merges and the clean-up PR lands with the two prerequisites.
- **Pre-ship probes**, at the issue tree:
  - an import probe of every cited name;
  - a route probe: `GGMRed.stateLoopFun_eval` on a toy handler (one that answers every query with
    a fixed function), and the T4 `post` correspondence at `ℓ₁ = 0`;
  - a duplication probe (`exact?` on the S1 and S3 lemmas, the scaling lemma, and log append).
- **Suggested order:** the companion, T4, S1–S3, T1, then T2. If the budget runs short, T1
  complete beats T1 and T2 partial.

## ===== briefs/pass-shelat-ch5-8/gates/10-efficiency/worker-report.md =====

# Fill s2b-efficiency — final payload

**Worker** Claude. **Unit** `s2b-efficiency`. **Issue base**
`b50f0a416cbf0a9f05acf14a254ba53cd97a7701` on `cryptography/pass-shelat-ch2-4`. Package read at
exchange commit `81449bb35998cc291d2f083ab2b07ccbce7fb2a9`: `shasum -a 256 -c SHA256SUMS` all OK
(`evidence/logs/package-sha256.log`); `SOURCE-SHA256SUMS` all OK on the clean issue checkout
(`evidence/logs/source-sha256.log`). The proof branch `fill/s2b-efficiency` is local. It starts at the
issue base and its head is `bc53a51865103bc20bb4dfbbf2ad302078a9a363`. Lean 4.25.0; Mathlib at the
manifest revision `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.

## 1. Status

| Target | Declaration | Status |
|---|---|---|
| T1 | `exists_handlerMachine` | **proved** |
| T2 | `exists_interactiveHandlerMachine` | **proved** |
| Companion | `exists_toCompOn_of_toComp` | **proved** |
| T4 | `exists_toOracleAdversary_of_bitCodec` | **proved** |

The four targets have no remaining admissions. Each target uses only the axioms
`propext`, `Classical.choice` and `Quot.sound` (`evidence/logs/axioms.log`).

The statements, every non-target declaration and the statement prose of all docstrings are
unchanged. A script compared all 28 declarations of `Efficiency.lean` against the base: their
statements and their docstrings up to `**Proof sketch` are identical, and only the four target
sketches differ. Global simp attributes are unchanged. No new `@[simp]` was added and no
`private` declaration was used.

Checkpoints delivered on `exchange/pass-shelat-ch5-8` (`fill s2b-efficiency: checkpoint 1` …
`4`): companion, T1, T4, T2. The fifth patch was added after checkpoint 4, following the
explicit-unfold scan (§6.3).

## 2. Changed files (`patches/` = the full `git format-patch` series from the issue base; `src/`)

| File | Lines | Change |
|---|---:|---|
| `TCSlib/Cryptography/Games/Efficiency.lean` | 706 | four proof bodies, four sketches (EF-2), six imports, module docstring |
| `TCSlib/Cryptography/Games/Efficiency/Strings.lean` | 549 | new (EF-1): S1 string layer, activation loop, machine glue |
| `TCSlib/Cryptography/Games/Efficiency/Replay.lean` | 117 | new: S3 replay lemma, cost scaling |
| `TCSlib/Cryptography/Games/Efficiency/Handler.lean` | 516 | new: T1 raw machine and functional equation |
| `TCSlib/Cryptography/Games/Efficiency/OracleBridge.lean` | 321 | new: T4 translators and evaluation lemma |
| `TCSlib/Cryptography/Games/Efficiency/Interactive.lean` | 838 | new: T2 replay machine, polynomial time, round lemmas |
| `TCSlib/Cryptography/Games/Efficiency/InteractiveSpec.lean` | 849 | new: T2 functional equation |

All helper files are under 1000 lines, and all new declarations are in the namespace
`TCSlib.Cryptography.Games.EffFill`. The imports are precise and acyclic.
`Strings` is the first consumer of the GGM reduction module and imports
`TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Reduction` directly. The helpers add no
new Mathlib root: the recomputed roots are identical to the supplied 68
(`evidence/logs/mathlib-roots-final.txt`). The order with the helpers inserted before
`Games/Efficiency` is `evidence/logs/order-final.txt` (143 modules). A check confirmed that every
`import TCSlib…` of every module appears earlier in that order.
`Efficiency.lean` is now a facade, so it imports every child module and lists them under
`## Contents`.

Commits (`patches/0001…0005`):
1. `46fb87d…` companion; 2. `d7d3623…` T1 (+`Strings`, `Handler`); 3. `a695df2…` T4
(+`OracleBridge`); 4. `4a04a94…` T2 (+`Replay`, `Interactive`, `InteractiveSpec`); 5. `bc53a51…`
replaces `simp only [id, …]` by `id_eq` and the simproc `reduceCtorEq` by `List.cons_ne_nil`.

**Edit to the module docstring.** The title no longer says "skeleton". The "Status: skeleton"
paragraph now says "Status: proved", and a `## Contents` section was added. The maintainer may
prefer other wording.

## 3. The proofs

**Companion.** `NUPPT.exists_comp A polyTimeComputable_pairSndD polyTimeComputable_id`. `φ` is
`NUPPT.coinsCongr` (`runAt_coinsCongr`), then `pairSndD_pairEncode`, `runAt_eq`, `toCompOn_eq` and
`toComp_eq`.

**T1.** `B := EffFill.exists_splitMachine A (hRaw_poly …) adv (n ↦ ⟨A.advice n, H.init n⟩) _
H.seedLen`, built from `NUPPT.ofPolyTime` and then `NUPPT.exists_split`.
- **The initial state is advice.** `init` is an arbitrary function of `n`, so `B` is non-uniform
  even when `A` is uniform. The advice bound is `2·A.adv + 2 + stateLen`.
- **The loop.** `EffFill.hRaw` is the activation loop `actLoop` over `GGMRed.stateLoopFun`, with at
  most `q + 1` rounds. Its state is `⟨encodeLog hist, ⟨s, 1^t⟩⟩`, and the context and `A`'s input
  are recomputed in every round.
- **A round.** The move goes through the canonical decoder (`canonWord_eq`). The answer is decoded
  componentwise with `fixLen` (`ofFn_getD_decodeFin`, `answer_of_pairDecode_eq_none/some`), which
  includes the case where `run`'s output is not a pair. A query at `t = q(n)` gives
  `0^{dα(n)}`, as `buildComp_zero_of_query` does.
- **The functional equation.** `hRaw_spec` is an induction on the remaining budget. It uses
  `GGMRed.stateLoopFun_eval`, wrapped as `runsTo_stop`, at the exact stopping round.

**T4.** `B' := NUPPT.exists_comp B bridgePre_poly bridgePost_poly` and `φ := coinsCongr`.
- `bridgePre` emits one piece per suffix, using `polyTimeComputable_iterateEmit` with the step
  `pairSndD`. `bridgePre_encodeHist` maps the history of a log to `⟨[], encodeLog⟩`, with
  `1^0 = []` for the index of the only oracle.
- `bridgePost_spec` shows that both decoders read corresponding moves on every word. This
  includes a payload of the wrong length (the verdict `false` on both sides), `ℓ₁(n) = 0` (an empty
  payload is a valid query), the word `⟨[true], [false]⟩`, and the default verdict.
- `eval_buildTree_bridge` is an induction on the budget. At the timeout, the verdict `false` is
  bit `0` of `zeroBits 1`.

**T2.** `B := exists_splitMachine` of `EffFill.iRaw`, with the same advice as T1.
- **The replay machine.** On `⟨z, O⟩` it replays the reduction, one activation per round. The
  state is `iSt ph L s 1^b cur L' 1^c O'`, where `O'` is the part of the log not yet replayed.
- **Defaults.** The joint default of `call`, at budget `0` or on a malformed result, splits into
  `0^{dout}` and `0^{stateLen}`. A pending query at budget `0` gives the timeout without asking
  its oracle, for the adversary, for a call and for the finalization.
- **The round bound.** `2 + finCall + q·(perCall + 2)`, which equals the design's
  `(q + 1) + q·(perCall + 1) + finCall + 1`. No extra initialization activation is needed, since
  `iStart` computes the initial state.
- **Cost bound.** The reduction tree is `CostBoundedBy (fun _ => 1) (q·perCall + finCall)`, from
  `toCompOn_costBoundedBy`, `costBoundedBy_mul` (the probe's scaling lemma),
  `buildComp_costBoundedBy`, `simulate_costBoundedBy` and `CostBoundedBy.bind`. These bounds are
  proved before the replay lemma is used.
- **The replay.** The machine's next-move function replays the tree from the empty log
  (`ReplaysFrom`). The invariant `IInv` quantifies over every extension of the replayed prefix,
  and three nested inductions cover the phases: `adv_phase` on the adversary's budget, then
  `call_phase` and `fin_phase` on the call and finalization budgets. Outer answers are arbitrary
  and are copied from `O` without being checked.
- **Conclusion.** `buildComp_of_replaysFrom` gives the equality of computation trees.
  `impl_apply`, `call_eq`, `input_eq`, `finish_eq`, `finInput_eq` and `seedIn_eq` match `H` with
  the raw `EffFill.iImpl` and `iFinish`.

## 4. Published helpers cited

These are the providers named in the brief, each read only through its public lemmas:
- **Machines and closure.** `NUPPT.coinLen_eq`, `runAt_eq`, `runAtL_eq_output_layout`,
  `runAtL_ofPolyTime`, `coins_ofPolyTime`, `coinsCongr`, `runAt_coinsCongr`, `exists_comp`,
  `exists_split`, `layout_eq`, `in*_layout`, `advInput_eq`, `polyTimeComputable_output`.
- **PRF layer.** `decodeOracleMove_pairEncode_ofFn`, `_pairEncode_false_of_length_ne`,
  `_true_two`; `decodeFin_eq`, `decodeFin_ofFn`, `decodeFin_eq_some_iff`.
- **GGM loop.** `GGMRed.stateLoopFun`, `stateLoopFun_poly`, `stateLoopFun_eval`,
  `pairEncode_append_right`; `StateLoop.orbit_zero/succ`, `lenLe_comp`, `unaryPoly_comp`,
  `cons_poly`; `polyTimeComputable_iterateEmit`.
- **Codec and machines.** `decodeBitMove_query/ret/of_not_canonical`, `encodeBitMove_query/ret`,
  `bitCodec_decodeMove/encodeEntry/timeout`, `encodeLog_bitCodec`, `ofFn_zeroBits`,
  `zeroBits_apply`; `NUPPT.toComp_eq`, `toCompOn_eq`, `toCompOn_costBoundedBy`, `buildComp_*`
  case lemmas, `buildComp_costBoundedBy`.
- **Simulation and evaluation.** `simulate_pure/query`, `simulate_costBoundedBy`,
  `OracleComp.pure_bind/query_bind/bind_assoc`, `costBoundedBy_query/pure`, `CostBoundedBy.bind`;
  `OracleComp.evalFn_pure/query`, `QueryTree.eval_ret/query`, `toOracleAdversary_eq`,
  `buildTree_*` case lemmas, `encodeHist_cons/nil`.
- **Pairing calculus.** `takeLen_poly`, `dropLen_poly`, `EnsembleLemmas.polyTimeComputable_zeros`,
  and the pairing combinators (`polyTimeComputable_pairEq`, `_lenEq`, `_lenLe`, `_ite`, `_and`,
  `_or`, `_not`, `_isNil`, `_tail`, `_unary`, `_unaryPoly`, `_const`).

The proofs did not need `toComp_singleCodec` or `decodeIdx_*`. The provider files and their proof
bodies are untouched. Inherited dependency findings, such as `StateLoop.gstep` inside
`GGMRed.stateLoopFun_poly`, stay in the cleanup ledger.

**Missing readers: none.** Every definition of another file had a published lemma.

## 5. New shared helpers (namespace `EffFill`) and requests

- **Requested for the shared layer (S1).** `encodeLog_append_single`, `length_encodeLog_le`,
  `fixLen` (+`ofFn_getD_decodeFin`, `fixLen_poly`), `selLen`/`sumPoly`, `canonWord`/`canonFun`
  (+`canonWord_eq`, `canonFun_poly`), `actLoop`/`RunsTo`
  (+`runsTo_zero/succ/stop`, `actLoop_poly`), `exists_splitMachine`, `entryPoly`,
  `exists_ofFn_eq`.
- **Requested for the shared layer (S3).** `ReplaysFrom`, `buildComp_of_replaysFrom` and
  `costBoundedBy_mul`. The scaling lemma is the supplied probe's statement with `p` in place of
  `scale * cost`.
- **Target-specific (stay in `EffFill`).** `hRaw` and its round, `iRaw` and its round, `iSt` and
  its readers, `iCall`/`iImpl`/`iFinish` (the raw terms of `InteractiveHandler.call/impl/finish`),
  and the bridge translators.
- **Duplication disclosure.**
  - **The handler round.** `hAct`/`hRaw` repeat the structure of GGM's round (`GGMRed.step`,
    `rawFun`) generically, as the design anticipated, until F-4.
  - **Small wrappers.** `zeros_poly`, `eq_poly`, `lenEq_poly` are applied forms of
    `EnsembleLemmas.polyTimeComputable_zeros`, `polyTimeComputable_pairEq` and `_lenEq`.
  - **Generalized GGM lemmas.** `encodeLog_append_single` generalizes
    `GGMRed.histEnc_append_single` to any codec. `length_le_length_encodeHist` and
    `length_encodeLog_le` follow `GGMRed.length_histEnc`.
  - **Mathlib-adjacent.** `ofFn_take_drop_add` restates `List.ofFn_add` with `take`/`drop`.
    `exists_ofFn_eq` may duplicate a Mathlib lemma.
  - No proof is copied verbatim.
- **Public definitions without lemmas: none.** Every public definition has its `_eq`/`_iff`
  lemma, so check 8 of the campaign lint is clean.

## 6. Evidence

### 6.1 Environment (addendum v1)

- **Preflight** (`logs/preflight.log`). `nproc` 4. Cgroup v1 with no memory limit, so the headroom
  is `MemAvailable` = 15.18 GiB; memory in use is 34.9 MiB (`usage − total_cache + total_shmem`).
  25.33 GiB were free on `/dev/vda` (ext4); no tmpfs was used. **Pass.** Lean 4.25.0 was
  installed with `elan` after the preflight (`logs/toolchain.log`). The re-check before the cache
  showed 23.95 GB free.
- **Cache.** The archive store was absent before the fetch (`logs/cache-store.log`). The fetch
  used 68 roots, identical to `roots.txt`: `Attempting to download 2066 file(s)`,
  `Decompressing 2066`, `Completed successfully`, exit 0 (`logs/cache-get.log`). There is no
  zero-size olean, and the root probe passes (`logs/cache-probe.log`).
- **Packages** (`logs/packages-check.log`). Every present package matches the manifest. ABSENT:
  `doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean`; no module of the order imports them. Last
  line: `RESULT: all present packages match the manifest`.
- **Bootstrap** (`logs/bootstrap.log`). Modules 1–130 of `order.txt`, everything before
  `Games/Efficiency`, built first: 130/130 exit 0.
  - The detached background sweep was ended twice, while checking `Build/Primitives`. A sampler
    started alongside was ended at the same moment, and there was no OOM event (`oom_kill 0`).
  - A standalone check of `Primitives` passed (1:35, 2.40 GB).
  - All later sweeps ran in the foreground, in chunks of at most four minutes, one Lean process at
    a time.
- **Resources.** Peak RSS was 2.67 GB (`Efficiency`-area modules). The longest module was 69 s.
  Per-module start, end, time and max RSS are in every log.

### 6.2 Checks

- **Checkpoints.** `logs/checks-cp1.log` … `checks-cp4.log` record the module checks at each
  checkpoint.
- **Final sweep** (`logs/sweep.log`, proof-branch `bc53a51`). All 143 modules of `order-final.txt`
  passed, exit 0, including `Games/Efficiency` and the downstream `Advantage`,
  `Bridges/Experiments`, `Protocols`, `ZeroKnowledge/Interaction`, `Bridges/Strategies` and the
  `Bridges` facade. The new modules have no error and no warning.
- **Admissions** (`logs/sorry-census.txt`). 18 sorry warnings. This is `base-sorries.txt` (22)
  minus exactly the four `Games/Efficiency` targets. The owner check of `Games/Efficiency` has no
  sorry warning.
- **Axioms** (`logs/axioms.log`, `seal/AxiomsS2b.lean`). The four targets, `hRaw_spec`,
  `iRaw_spec`, `eval_buildTree_bridge` and `canonWord_eq` use
  `[propext, Classical.choice, Quot.sound]`. `buildComp_of_replaysFrom` uses `[propext, Quot.sound]`.
- **Lint.** `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Games --check8b` gives
  0 FAIL and 0 WARN both before (14 files, base worktree) and after (20 files)
  (`logs/lint-before.log`, `logs/lint-after.log`).

### 6.3 Seal (`logs/seal-scan.log`, `logs/seal.log`, sources in `seal/`)

- **Scan** (`SealScan.lean`). The roots are every declaration of the six helper modules plus the
  four targets: 262 roots, 316 declarations scanned with their auxiliary declarations (matchers,
  `proof_`, `eq_`, internal names).
  - **89 foreign TCSlib definitions** were found. Of these, **69 are non-reducible and sealable**.
    They include `pairEncode`, `pairDecode`, `pairFstD`, `pairSndD`, `PolyExpr.eval`,
    `PolyTimeComputable`, `NUPPT.{output, runAt, runAtL, layout, in*, coinLen, ofPolyTime,
    toComp, toCompOn, toOracleAdversary, coinsCongr, advInput}`, `StateLoop.orbit`,
    `GGMRed.stateLoopFun`, `buildComp`, `simulate`, `OracleComp.{bind, CostBoundedBy, evalFn}`,
    `MachineCodec.encodeLog`, `bitCodec`, `decodeBitMove`, `encodeBitMove`, `zeroBits`,
    `decodeFin`, `decodeOracleMove`, `encodeHist`, `buildTree`, `QueryTree.eval`.
  - Helper definitions are also sealed wherever another module uses them, for example
    `canonWord`, `fixLen`, `actLoop`, `iRaw` and `iImpl` inside `Efficiency.lean`.
  - **Instances:** the scan flags every instance, and none of the foreign definitions is a TCSlib
    instance.
  - **Not sealable (20).** Reducible abbreviations, projections and auxiliary recursors such as
    `NUPPT.Coins`, `bitSpec`, `QueryLog`, `QueryImpl`, `unifSpec`, `QueryTree`/`.ret`/`.query`,
    `OracleSpec.dom/rng`, `MachineCodec.decodeMove/encodeEntry/timeout`, `NUPPT.advice/coins/adv`,
    `Move.casesOn`, `OracleComp.casesOn/brecOn/below`. These are notation.
- **Sealed copies.** Verbatim copies of each helper module and of `Efficiency.lean` were checked
  with every foreign definition they use made irreducible. Each copy imports only the original's
  imports. All seven elaborate with exit 0 and no warning (`Seal*.lean`). `PolyExpr.eval` was
  sealed too, and the code reads it only through `eval_add/mul/const/var`.
- **Controls.** Six readings through a body: `pairEncode`, `encodeLog []`, `EffFill.fixLen`,
  `PolyExpr.eval (.const 3)`, `buildComp` at budget 0, and `EffFill.actLoop`. **All six pass
  unsealed and fail sealed**, at lines 18, 21, 24, 27, 31 and 36 of `SealControlsSealed.lean`, so
  the seal is active.
- **Explicit-unfold scan** (`seal/RwIds.lean`, `logs/rwids.log`, `logs/rwids-files.tsv`).
  `irreducible` does not block `rw [f]`, `simp [f]` or `unfold f`, so a separate scan collected
  every identifier passed to `rw`, `rwa`, `simp`, `simp only`, `simp_rw`, `dsimp` or `unfold` in
  the added lines: 284 in total.
  - 234 are theorems and 41 are local hypotheses or text fragments.
  - The 9 definitions are each passed only in their own file: `canonFun` in `Strings`; `gPh`,
    `gLin`, `gS`, `gB`, `gCur`, `gLc`, `gC`, `gO` in `Interactive`.
  - No core, Mathlib or foreign TCSlib definition is passed. The scan found `simp only [id]` and the
    simproc `reduceCtorEq`, and commit 5 removed both.

**Readings disclosed: none of a foreign definition.**

## 7. Notes for the maintainer

- **Elaboration cost.** The new modules elaborate in under 15 s each. Two patterns were very slow when the
  terms were not syntactically identical: re-elaborating a `Σ` literal such as `⟨j, x', y⟩` inside a
  dependent invariant, and propagating an expected type into lemmas with many implicit section
  variables. `InteractiveSpec` avoids both by taking these terms from the goal (`_`) and by
  building the invariant in tactic mode (`beta_reduce`).
- **Scope of the statements.** As in the design, `B`'s running time is polynomial in `n + |z|`,
  and `B` is non-uniform.

**Final payload delivered — ready for maintainer review and the gate**

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

## ===== TCSlib/Cryptography/Games/Efficiency/Handler.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Efficiency.Strings
import TCSlib.Cryptography.Games.Simulate

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The machine of a non-interactive handler (efficiency fill, T1)

The raw function behind `Games.exists_handlerMachine` (route note
`briefs/pass-shelat-ch5-8/design/S2b-efficiency.md`, §"T1"), stated over the raw ingredients of a
handler (its lengths and its three string functions) so that it does not depend on the handler
structure of `TCSlib.Cryptography.Games.Efficiency`.

On the raw layout `X = ⟨⟨⟨1^n, ⟨z, ω⟩⟩, ⟨α_A, s₀⟩⟩, r⟩` (`α_A` the adversary's advice, `s₀` the
initial state) the function is an activation loop (`EffFill.actLoop`) on the state
`⟨L, ⟨s, 1^t⟩⟩`: the adversary's encoded log, the handler's state and the number of answered
queries. One round runs the adversary on `⟨advIn ⟨1^n, ⟨z, ω⟩⟩, L⟩`, reads its move through the
canonical decoder, and either stops (an output, or a query when the budget `q(n)` is spent) with
`out ⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, a⟩⟩`, or answers the query with `run`, decoded componentwise with the
all-`false` default (`fixLen`), and appends the entry to the log.

## Main definitions

* `EffFill.hAct`, `EffFill.hStart`, `EffFill.hRaw`: the round, the initial state and the raw
  function; `EffFill.hRounds`, `EffFill.hBound`: the round and state bounds; `EffFill.hState`: the
  state.
* `EffFill.advNext`: the next-move function of a machine adversary on an input.

## Main results

* `EffFill.hRaw_poly`: the raw function is polynomial-time.
* `EffFill.hRaw_spec`: on the layout, it returns the finalized output of the simulation.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §2.1 (closure of p.p.t. machines under efficient operations; for example the reductions of the
  proofs of Theorems 135.4 and 168.2).
-/

namespace TCSlib.Cryptography.Games.EffFill

open Complexity Turing

variable {k : ℕ}

/-- The next-move function of the machine `A` on the input `x` with coins `r`: `A`'s output on
`⟨x, encoded log⟩`, decoded by the codec. -/
def advNext {ι α : Type} {spec : OracleSpec ι} (A : NUPPT) (codec : MachineCodec spec α) (n : ℕ)
    (x : List Bool) (r : A.Coins n) (hist : QueryLog spec) : Move spec α :=
  codec.decodeMove (A.runAt n (pairEncode x (codec.encodeLog hist)) r)

/-- `advNext A codec n x r hist = codec.decodeMove (A.runAt n ⟨x, codec.encodeLog hist⟩ r)`. -/
theorem advNext_eq {ι α : Type} {spec : OracleSpec ι} (A : NUPPT) (codec : MachineCodec spec α)
    (n : ℕ) (x : List Bool) (r : A.Coins n) (hist : QueryLog spec) :
    advNext A codec n x r hist = codec.decodeMove (A.runAt n (pairEncode x (codec.encodeLog hist))
        r) :=
  rfl

/-- `A`'s computation on the input `x` is `buildComp` of `advNext` (`NUPPT.toCompOn_eq`). -/
theorem toCompOn_eq_advNext {ι α : Type} {spec : OracleSpec ι} (A : NUPPT)
    (codec : MachineCodec spec α) (n q : ℕ) (x : List Bool) (r : A.Coins n) :
    A.toCompOn codec n q x r = buildComp (advNext A codec n x r) codec.timeout q [] := by
  rw [NUPPT.toCompOn_eq]
  rfl

section Raw

variable (A : NUPPT) (q dα : PolyExpr) (din dout : Fin k → PolyExpr) (stateLen : PolyExpr)
  (run advIn out : List Bool → List Bool)

/-- The context `⟨1^n, ⟨z, ω⟩⟩` read off the raw layout `X` (its parameter and argument). -/
def hCtx (X : List Bool) : List Bool := pairEncode (NUPPT.inParam X) (NUPPT.inArg X)

/-- `hCtx X = ⟨inParam X, inArg X⟩`. -/
theorem hCtx_eq (X : List Bool) : hCtx X = pairEncode (NUPPT.inParam X) (NUPPT.inArg X) := rfl

/-- The adversary's canonical move word in the round on `w = ⟨X, ⟨L, ⟨s, c⟩⟩⟩`. -/
def hMove (w : List Bool) : List Bool :=
  canonFun din (pairEncode (NUPPT.inParam (pairFstD w))
    (pairEncode (List.replicate (dα.eval (NUPPT.inParam (pairFstD w)).length) true)
      (A.output (NUPPT.layout (NUPPT.inParam (pairFstD w))
        (pairEncode (advIn (hCtx (pairFstD w))) (pairFstD (pairSndD w)))
        (pairFstD (NUPPT.inAdvice (pairFstD w))) (NUPPT.inCoins (pairFstD w))))))

/-- The defining equation of `hMove` (the canonical decoder of `A`'s output on
`⟨advIn ctx, L⟩`). -/
theorem hMove_eq (w : List Bool) :
    hMove A dα din advIn w =
      canonFun din (pairEncode (NUPPT.inParam (pairFstD w))
        (pairEncode (List.replicate (dα.eval (NUPPT.inParam (pairFstD w)).length) true)
          (A.output (NUPPT.layout (NUPPT.inParam (pairFstD w))
            (pairEncode (advIn (hCtx (pairFstD w))) (pairFstD (pairSndD w)))
            (pairFstD (NUPPT.inAdvice (pairFstD w))) (NUPPT.inCoins (pairFstD w)))))) :=
  rfl

/-- The handler's output `run ⟨ctx, ⟨s, ⟨1^i, x⟩⟩⟩` on the pending query of the round. -/
def hRes (w : List Bool) : List Bool :=
  run (pairEncode (hCtx (pairFstD w))
    (pairEncode (pairFstD (pairSndD (pairSndD w))) (pairSndD (hMove A dα din advIn w))))

/-- The defining equation of `hRes`. -/
theorem hRes_eq (w : List Bool) :
    hRes A dα din run advIn w =
      run (pairEncode (hCtx (pairFstD w))
        (pairEncode (pairFstD (pairSndD (pairSndD w))) (pairSndD (hMove A dα din advIn w)))) :=
  rfl

/-- The new state of a continuing round: the log with the answered entry appended, the new state
and the incremented counter. -/
def hNext (w : List Bool) : List Bool :=
  pairEncode
    (pairFstD (pairSndD w) ++ pairEncode (pairEncode (pairFstD (pairSndD (hMove A dα din advIn w)))
      (pairEncode (pairSndD (pairSndD (hMove A dα din advIn w)))
        (fixLen (selLen dout (NUPPT.inParam (pairFstD w)).length
          (pairFstD (pairSndD (hMove A dα din advIn w))).length)
          (pairFstD (hRes A dα din run advIn w))))) [])
    (pairEncode (fixLen (stateLen.eval (NUPPT.inParam (pairFstD w)).length)
      (pairSndD (hRes A dα din run advIn w))) (true :: pairSndD (pairSndD (pairSndD w))))

/-- The defining equation of `hNext`. -/
theorem hNext_eq (w : List Bool) :
    hNext A dα din dout stateLen run advIn w =
      pairEncode
        (pairFstD (pairSndD w) ++ pairEncode (pairEncode (pairFstD (pairSndD (hMove A dα din advIn
            w)))
          (pairEncode (pairSndD (pairSndD (hMove A dα din advIn w)))
            (fixLen (selLen dout (NUPPT.inParam (pairFstD w)).length
              (pairFstD (pairSndD (hMove A dα din advIn w))).length)
              (pairFstD (hRes A dα din run advIn w))))) [])
        (pairEncode (fixLen (stateLen.eval (NUPPT.inParam (pairFstD w)).length)
          (pairSndD (hRes A dα din run advIn w))) (true :: pairSndD (pairSndD (pairSndD w)))) :=
  rfl

/-- **One round of the handler machine** on `w = ⟨X, ⟨L, ⟨s, c⟩⟩⟩`: stop with
`out ⟨ctx, ⟨s, a⟩⟩` on an output `a`; stop with `out ⟨ctx, ⟨s, 0^{dα(n)}⟩⟩` on a query when
`q(n) ≤ |c|`; otherwise continue with `hNext`. -/
def hAct (w : List Bool) : List Bool :=
  if pairFstD (hMove A dα din advIn w) = [true] then
    pairEncode [true] (out (pairEncode (hCtx (pairFstD w))
      (pairEncode (pairFstD (pairSndD (pairSndD w))) (pairSndD (hMove A dα din advIn w)))))
  else if q.eval (NUPPT.inParam (pairFstD w)).length ≤ (pairSndD (pairSndD (pairSndD w))).length
      then
    pairEncode [true] (out (pairEncode (hCtx (pairFstD w))
      (pairEncode (pairFstD (pairSndD (pairSndD w)))
        (List.replicate (dα.eval (NUPPT.inParam (pairFstD w)).length) false))))
  else pairEncode [false] (hNext A dα din dout stateLen run advIn w)

/-- The defining equation of `hAct`. -/
theorem hAct_eq (w : List Bool) :
    hAct A q dα din dout stateLen run advIn out w =
      if pairFstD (hMove A dα din advIn w) = [true] then
        pairEncode [true] (out (pairEncode (hCtx (pairFstD w))
          (pairEncode (pairFstD (pairSndD (pairSndD w))) (pairSndD (hMove A dα din advIn w)))))
      else if q.eval (NUPPT.inParam (pairFstD w)).length ≤
          (pairSndD (pairSndD (pairSndD w))).length then
        pairEncode [true] (out (pairEncode (hCtx (pairFstD w))
          (pairEncode (pairFstD (pairSndD (pairSndD w)))
            (List.replicate (dα.eval (NUPPT.inParam (pairFstD w)).length) false))))
      else pairEncode [false] (hNext A dα din dout stateLen run advIn w) :=
  rfl

/-- The initial state `⟨[], ⟨s₀, []⟩⟩`, with the initial state `s₀` read off the advice. -/
def hStart (X : List Bool) : List Bool :=
  pairEncode [] (pairEncode (pairSndD (NUPPT.inAdvice X)) [])

/-- `hStart X = ⟨[], ⟨snd (inAdvice X), []⟩⟩`. -/
theorem hStart_eq (X : List Bool) :
    hStart X = pairEncode [] (pairEncode (pairSndD (NUPPT.inAdvice X)) []) := rfl

/-- The round bound `q + 1`: at most `q(n)` answered queries and one stopping round. -/
def hRounds : PolyExpr := .add q (.const 1)

/-- `hRounds q = q + 1`. -/
theorem hRounds_eq : hRounds q = .add q (.const 1) := rfl

/-- The state bound `2 q E + 2 stateLen + q + 4` (`E` the entry bound `entryPoly`). -/
def hBound : PolyExpr :=
  .add (.mul (.const 2) (.mul q (entryPoly din dout))) (.add (.mul (.const 2) stateLen) (.add q
      (.const 4)))

/-- The defining equation of `hBound`. -/
theorem hBound_eq : hBound q din dout stateLen =
    .add (.mul (.const 2) (.mul q (entryPoly din dout))) (.add (.mul (.const 2) stateLen) (.add q
        (.const 4))) :=
  rfl

/-- **The raw function of the handler machine:** the activation loop of `hAct` from `hStart`, with
`q + 1` rounds and the state bound `hBound`. -/
def hRaw : List Bool → List Bool :=
  actLoop hStart (hAct A q dα din dout stateLen run advIn out) (hRounds q) (hBound q din dout
      stateLen)

/-- `hRaw = actLoop hStart hAct (q + 1) hBound`. -/
theorem hRaw_eq : hRaw A q dα din dout stateLen run advIn out =
    actLoop hStart (hAct A q dα din dout stateLen run advIn out) (hRounds q)
      (hBound q din dout stateLen) :=
  rfl

/-! ### Polynomial time -/

variable {run advIn out}

/-- The context is polynomial-time. -/
theorem hCtx_poly : PolyTimeComputable hCtx :=
  NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inArg

/-- The round's move is polynomial-time. -/
theorem hMove_poly (hadvIn : PolyTimeComputable advIn) : PolyTimeComputable (hMove A dα din advIn)
    := by
  have hX := polyTimeComputable_pairFstD
  have hu := NUPPT.polyTimeComputable_inParam.comp' hX
  have hout := A.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout hu
    ((hadvIn.comp' (hCtx_poly.comp' hX)).pairEncode
      (polyTimeComputable_pairFstD.comp' polyTimeComputable_pairSndD))
    (polyTimeComputable_pairFstD.comp' (NUPPT.polyTimeComputable_inAdvice.comp' hX))
    (NUPPT.polyTimeComputable_inCoins.comp' hX))
  exact (canonFun_poly din).comp' (hu.pairEncode ((StateLoop.unaryPoly_comp dα hu).pairEncode hout))

/-- The handler's output on the pending query is polynomial-time. -/
theorem hRes_poly (hrun : PolyTimeComputable run) (hadvIn : PolyTimeComputable advIn) :
    PolyTimeComputable (hRes A dα din run advIn) :=
  hrun.comp' ((hCtx_poly.comp' polyTimeComputable_pairFstD).pairEncode
    ((polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp'
      polyTimeComputable_pairSndD)).pairEncode
      (polyTimeComputable_pairSndD.comp' (hMove_poly A dα din hadvIn))))

/-- The continuing state is polynomial-time. -/
theorem hNext_poly (hrun : PolyTimeComputable run) (hadvIn : PolyTimeComputable advIn) :
    PolyTimeComputable (hNext A dα din dout stateLen run advIn) := by
  have hX := polyTimeComputable_pairFstD
  have hu := NUPPT.polyTimeComputable_inParam.comp' hX
  have hm := hMove_poly A dα din hadvIn
  have hq := polyTimeComputable_pairSndD.comp' hm
  have hres := hRes_poly A dα din hrun hadvIn
  have hy := fixLen_poly ((selLen_poly dout).comp' (hu.pairEncode (polyTimeComputable_pairFstD.comp'
      hq)))
    (polyTimeComputable_pairFstD.comp' hres)
  have hs := fixLen_poly (StateLoop.unaryPoly_comp stateLen hu) (polyTimeComputable_pairSndD.comp'
      hres)
  have h := ((polyTimeComputable_pairFstD.comp' polyTimeComputable_pairSndD).append
    (((polyTimeComputable_pairFstD.comp' hq).pairEncode
      ((polyTimeComputable_pairSndD.comp' hq).pairEncode hy)).pairEncode
        (polyTimeComputable_const []))).pairEncode
    (hs.pairEncode ((StateLoop.cons_poly true).comp' (polyTimeComputable_pairSndD.comp'
      (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD))))
  refine h.congr fun w => ?_
  rw [hNext_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]

/-- **One round of the handler machine is polynomial-time.** -/
theorem hAct_poly (hrun : PolyTimeComputable run) (hadvIn : PolyTimeComputable advIn)
    (hout : PolyTimeComputable out) : PolyTimeComputable (hAct A q dα din dout stateLen run advIn
        out) := by
  have hX := polyTimeComputable_pairFstD
  have hu := NUPPT.polyTimeComputable_inParam.comp' hX
  have hm := hMove_poly A dα din hadvIn
  have hctx := hCtx_poly.comp' hX
  have hst := polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp'
    polyTimeComputable_pairSndD)
  have hc := polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairSndD.comp'
    polyTimeComputable_pairSndD)
  have h1 := eq_poly (polyTimeComputable_pairFstD.comp' hm) (polyTimeComputable_const [true])
  have h2 := StateLoop.lenLe_comp hc (StateLoop.unaryPoly_comp q hu)
  have hz : PolyTimeComputable fun w =>
      List.replicate (dα.eval (NUPPT.inParam (pairFstD w)).length) false :=
    (zeros_poly (StateLoop.unaryPoly_comp dα hu)).congr fun w => by rw [List.length_replicate]
  have h := polyTimeComputable_ite h1
    ((polyTimeComputable_const [true]).pairEncode (hout.comp' (hctx.pairEncode
      (hst.pairEncode (polyTimeComputable_pairSndD.comp' hm)))))
    (polyTimeComputable_ite h2
      ((polyTimeComputable_const [true]).pairEncode (hout.comp' (hctx.pairEncode (hst.pairEncode
          hz))))
      ((polyTimeComputable_const [false]).pairEncode (hNext_poly A dα din dout stateLen hrun
          hadvIn)))
  refine h.congr fun w => ?_
  rw [hAct_eq]
  simp only [List.length_replicate, decide_eq_true_eq]

/-- **The raw function of the handler machine is polynomial-time** (`actLoop_poly`). -/
theorem hRaw_poly (hrun : PolyTimeComputable run) (hadvIn : PolyTimeComputable advIn)
    (hout : PolyTimeComputable out) : PolyTimeComputable (hRaw A q dα din dout stateLen run advIn
        out) :=
  actLoop_poly ((polyTimeComputable_const []).pairEncode
      ((polyTimeComputable_pairSndD.comp' NUPPT.polyTimeComputable_inAdvice).pairEncode
        (polyTimeComputable_const [])))
    (hAct_poly A q dα din dout stateLen hrun hadvIn hout) _ _

end Raw

/-! ### The functional equation -/

section Spec

variable (A : NUPPT) (q dα : PolyExpr) (din dout : Fin k → PolyExpr) (stateLen : PolyExpr)
  (run advIn out : List Bool → List Bool)

/-- The state `⟨L, ⟨s, 1^t⟩⟩` of the handler machine: the encoded log, the handler's state and
the number `t` of answered queries. -/
def hState (L s : List Bool) (t : ℕ) : List Bool :=
  pairEncode L (pairEncode s (List.replicate t true))

/-- `hState L s t = ⟨L, ⟨s, 1^t⟩⟩`. -/
theorem hState_eq (L s : List Bool) (t : ℕ) :
    hState L s t = pairEncode L (pairEncode s (List.replicate t true)) :=
  rfl

/-- The move word of a round on the state `⟨L, ⟨s, 1^t⟩⟩` at parameter `n`: the canonical decoder
of `A`'s output on `⟨advIn ctx, L⟩` with the advice and coins of the layout. -/
theorem hMove_state {X : List Bool} {n : ℕ} (hXu : NUPPT.inParam X = List.replicate n true)
    (L s : List Bool) (t : ℕ) :
    hMove A dα din advIn (pairEncode X (hState L s t)) =
      canonWord din n (dα.eval n) (A.output (NUPPT.layout (List.replicate n true)
        (pairEncode (advIn (hCtx X)) L) (pairFstD (NUPPT.inAdvice X)) (NUPPT.inCoins X))) := by
  rw [hMove_eq, hState_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, hXu, List.length_replicate]
  exact canonFun_eq din n (dα.eval n) _

/-- **A round on an output stops:** if the move word is `⟨[true], a⟩`, the round stops with
`out ⟨ctx, ⟨s, a⟩⟩`. -/
theorem hAct_of_ret {X : List Bool} {L s a : List Bool} {t : ℕ}
    (hm : hMove A dα din advIn (pairEncode X (hState L s t)) = pairEncode [true] a) :
    hAct A q dα din dout stateLen run advIn out (pairEncode X (hState L s t)) =
      pairEncode [true] (out (pairEncode (hCtx X) (pairEncode s a))) := by
  rw [hAct_eq, hm, if_pos (pairFstD_pairEncode _ _)]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, hState_eq]

/-- **A query with the budget spent stops:** if the move word is a query `⟨[false], m⟩` and
`q(n) ≤ t`, the round stops with `out ⟨ctx, ⟨s, 0^{dα(n)}⟩⟩`. -/
theorem hAct_of_timeout {X : List Bool} {n : ℕ} (hXu : NUPPT.inParam X = List.replicate n true)
    {L s m : List Bool} {t : ℕ}
    (hm : hMove A dα din advIn (pairEncode X (hState L s t)) = pairEncode [false] m)
    (ht : q.eval n ≤ t) :
    hAct A q dα din dout stateLen run advIn out (pairEncode X (hState L s t)) =
      pairEncode [true] (out (pairEncode (hCtx X) (pairEncode s
        (List.replicate (dα.eval n) false)))) := by
  have hne : pairFstD (pairEncode [false] m) ≠ [true] := by
    rw [pairFstD_pairEncode]
    decide
  rw [hAct_eq, hm, if_neg hne]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, hState_eq, hXu, List.length_replicate]
  rw [if_pos ht]

/-- **A query within budget continues:** if the move word is the query `⟨[false], ⟨iw, xw⟩⟩` and
`t < q(n)`, the round continues with the entry `⟨iw, ⟨xw, y⟩⟩` appended to the log, the new state
`s'` and `t + 1`, where `y` and `s'` are `run ⟨ctx, ⟨s, ⟨iw, xw⟩⟩⟩` decoded componentwise. -/
theorem hAct_of_query {X : List Bool} {n : ℕ} (hXu : NUPPT.inParam X = List.replicate n true)
    {L s iw xw : List Bool} {t : ℕ}
    (hm : hMove A dα din advIn (pairEncode X (hState L s t)) =
      pairEncode [false] (pairEncode iw xw))
    (ht : t < q.eval n) :
    hAct A q dα din dout stateLen run advIn out (pairEncode X (hState L s t)) =
      pairEncode [false] (hState
        (L ++ pairEncode (pairEncode iw (pairEncode xw (fixLen (selLen dout n iw.length)
          (pairFstD (run (pairEncode (hCtx X) (pairEncode s (pairEncode iw xw)))))))) [])
        (fixLen (stateLen.eval n) (pairSndD (run (pairEncode (hCtx X) (pairEncode s
          (pairEncode iw xw)))))) (t + 1)) := by
  have hne : pairFstD (pairEncode [false] (pairEncode iw xw)) ≠ [true] := by
    rw [pairFstD_pairEncode]
    decide
  rw [hAct_eq, hm, if_neg hne, hNext_eq, hRes_eq, hm]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, hState_eq, hXu, List.length_replicate]
  rw [if_neg (Nat.not_le.2 ht), List.replicate_succ]

/-- **The functional equation of the handler machine.** At parameter `n`, on the layout
`X = ⟨⟨⟨1^n, ⟨z, ω⟩⟩, ⟨α_A, s₀⟩⟩, r⟩` with `α_A = A.advice n`, for any answer function `ans`
that agrees with `run` decoded componentwise (`fixLen`), the simulation of `A` on
`advIn ⟨1^n, ⟨z, ω⟩⟩` with the stateless answers `ans` from `s₀` returns some `(a, s)`, and the
raw function returns `out ⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, a⟩⟩`.

**Proof sketch.** By induction on the remaining budget `b`, from the round `t = q(n) − b` whose
state is `⟨encodeLog hist, ⟨s, 1^t⟩⟩` (`RunsTo`). The round's move word is the canonical word of
`A`'s next move (`hMove_state`, `canonWord_eq`, `NUPPT.runAtL_eq_output_layout`). On an output `a`
the round stops with `out ⟨ctx, ⟨s, a⟩⟩` (`hAct_of_ret`) and `buildComp` returns `a`
(`buildComp_zero_of_ret`, `buildComp_succ_of_ret`, `simulate_pure`). On a query with `b = 0` it
stops with the all-`false` output (`hAct_of_timeout`), as `buildComp_zero_of_query` does. On a
query with `b > 0` the round continues (`hAct_of_query`) with the answered entry appended
(`encodeLog_append_single`, `bitCodec_encodeEntry`) and the new state, which is the state of
`simulate` after `buildComp_succ_of_query`, `simulate_query` and `pure_bind`. The states stay
within `hBound` (`length_encodeLog_le`, `entry_le_entryPoly`, `PolyExpr.eval_mono`), and the
stopping
round is at most `q(n) ≤ (q + 1)(|X|)`; `runsTo_stop` evaluates the loop. -/
theorem hRaw_spec {ι' : Type} {spec' : OracleSpec ι'} (n : ℕ) (z ω : List Bool) (r : A.Coins n)
    (init : Fin (stateLen.eval n) → Bool)
    (ans : ∀ i : Fin k, (Fin ((din i).eval n) → Bool) → (Fin (stateLen.eval n) → Bool) →
      (Fin ((dout i).eval n) → Bool) × (Fin (stateLen.eval n) → Bool))
    (hans : ∀ i x s,
      List.ofFn (ans i x s).1 = fixLen ((dout i).eval n) (pairFstD (run (pairEncode
        (pairEncode (List.replicate n true) (pairEncode z ω))
        (pairEncode (List.ofFn s) (pairEncode (List.replicate i true) (List.ofFn x)))))) ∧
      List.ofFn (ans i x s).2 = fixLen (stateLen.eval n) (pairSndD (run (pairEncode
        (pairEncode (List.replicate n true) (pairEncode z ω))
        (pairEncode (List.ofFn s) (pairEncode (List.replicate i true) (List.ofFn x))))))) :
    ∃ (a : Fin (dα.eval n) → Bool) (s : Fin (stateLen.eval n) → Bool),
      simulate (spec' := spec') (fun i x s => OracleComp.pure (ans i x s))
          (A.toCompOn (bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n))
            n (q.eval n) (advIn (pairEncode (List.replicate n true) (pairEncode z ω))) r) init =
        .pure (a, s) ∧
      hRaw A q dα din dout stateLen run advIn out
          (NUPPT.layout (List.replicate n true) (pairEncode z ω)
            (pairEncode (A.advice n) (List.ofFn init)) (List.ofFn r)) =
        out (pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
          (pairEncode (List.ofFn s) (List.ofFn a))) := by
  -- The fixed data of the run.
  set X := NUPPT.layout (List.replicate n true) (pairEncode z ω)
    (pairEncode (A.advice n) (List.ofFn init)) (List.ofFn r) with hX
  set ctx := pairEncode (List.replicate n true) (pairEncode z ω) with hctx
  set codec := bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n)
    with hcodec
  have hnX : n ≤ X.length := le_length_layout n _ _ _
  have hXu : NUPPT.inParam X = List.replicate n true := NUPPT.inParam_layout _ _ _ _
  have hXctx : hCtx X = ctx := by rw [hCtx_eq, hXu, hX, NUPPT.inArg_layout]
  -- The move word of a round is the canonical word of `A`'s next move.
  have hmove : ∀ (hist : QueryLog (bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n)))
      (s : Fin (stateLen.eval n) → Bool) (t : ℕ), hMove A dα din advIn
      (pairEncode X (hState (codec.encodeLog hist) (List.ofFn s) t)) =
      encodeBitMove (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n)
        (advNext A codec n (advIn ctx) r hist) := by
    intro hist s t
    rw [hMove_state A dα din advIn hXu, hXctx, hX, NUPPT.inAdvice_layout, NUPPT.inCoins_layout,
      pairFstD_pairEncode, ← NUPPT.runAtL_eq_output_layout, ← NUPPT.runAt_eq,
      canonWord_eq din (fun i => (dout i).eval n), advNext_eq, hcodec, bitCodec_decodeMove]
  -- The state bound.
  have hbound : ∀ (hist : QueryLog (bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n)))
      (s : Fin (stateLen.eval n) → Bool) (t : ℕ), hist.length = t → t ≤ q.eval n →
      (hState (codec.encodeLog hist) (List.ofFn s) t).length ≤
        (hBound q din dout stateLen).eval X.length := by
    intro hist s t hlen ht
    have hlog := length_encodeLog_le codec ((entryPoly din dout).eval n) hist
      (fun e _ => entry_le_entryPoly din dout n e (dα.eval n))
    refine le_trans ?_ ((hBound q din dout stateLen).eval_mono hnX)
    rw [hState_eq, length_pairEncode, length_pairEncode, List.length_ofFn, List.length_replicate,
      hBound_eq]
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    rw [hlen] at hlog
    have : t * (entryPoly din dout).eval n ≤ q.eval n * (entryPoly din dout).eval n :=
      Nat.mul_le_mul_right _ ht
    omega
  have hR : ∀ t, t ≤ q.eval n → t ≤ (hRounds q).eval X.length := by
    intro t ht
    rw [hRounds_eq, PolyExpr.eval_add, PolyExpr.eval_const]
    have := q.eval_mono hnX
    omega
  -- The induction on the remaining budget.
  have key : ∀ b hist (s : Fin (stateLen.eval n) → Bool) t, t + b = q.eval n →
      hist.length = t →
      RunsTo hStart (hAct A q dα din dout stateLen run advIn out) (hBound q din dout stateLen) X t
        (hState (codec.encodeLog hist) (List.ofFn s) t) →
      ∃ (a : Fin (dα.eval n) → Bool) (s' : Fin (stateLen.eval n) → Bool),
        simulate (spec' := spec') (fun i x s => OracleComp.pure (ans i x s))
            (buildComp (advNext A codec n (advIn ctx) r) codec.timeout b hist) s = .pure (a, s') ∧
        hRaw A q dα din dout stateLen run advIn out X =
          out (pairEncode ctx (pairEncode (List.ofFn s') (List.ofFn a))) := by
    intro b
    induction b with
    | zero =>
      intro hist s t ht hlen hrun
      cases hm : advNext A codec n (advIn ctx) r hist with
      | ret a =>
        refine ⟨a, s, by rw [buildComp_zero_of_ret hm, simulate_pure], ?_⟩
        refine runsTo_stop hrun ?_ (hR t (by omega))
        rw [hAct_of_ret A q dα din dout stateLen run advIn out
          (by rw [hmove, hm, encodeBitMove_ret]), hXctx]
      | query i x =>
        refine ⟨zeroBits _, s, ?_, ?_⟩
        · rw [buildComp_zero_of_query hm, simulate_pure, hcodec, bitCodec_timeout]
        · refine runsTo_stop hrun ?_ (hR t (by omega))
          rw [hAct_of_timeout A q dα din dout stateLen run advIn out hXu
            (by rw [hmove, hm, encodeBitMove_query]) (by omega), hXctx, ofFn_zeroBits]
    | succ b ih =>
      intro hist s t ht hlen hrun
      cases hm : advNext A codec n (advIn ctx) r hist with
      | ret a =>
        refine ⟨a, s, by rw [buildComp_succ_of_ret hm, simulate_pure], ?_⟩
        refine runsTo_stop hrun ?_ (hR t (by omega))
        rw [hAct_of_ret A q dα din dout stateLen run advIn out
          (by rw [hmove, hm, encodeBitMove_ret]), hXctx]
      | query i x =>
        have hlen' : (hist ++ [(⟨i, x, (ans i x s).1⟩ : Σ i, (bitSpec (fun i => (din i).eval n)
            (fun i => (dout i).eval n)).dom i × (bitSpec (fun i => (din i).eval n)
            (fun i => (dout i).eval n)).rng i)]).length = t + 1 := by
          rw [List.length_append, hlen, List.length_singleton]
        have hnext : hAct A q dα din dout stateLen run advIn out
            (pairEncode X (hState (codec.encodeLog hist) (List.ofFn s) t)) =
            pairEncode [false] (hState (codec.encodeLog (hist ++ [⟨i, x, (ans i x s).1⟩]))
              (List.ofFn (ans i x s).2) (t + 1)) := by
          rw [hAct_of_query A q dα din dout stateLen run advIn out hXu
            (by rw [hmove, hm, encodeBitMove_query]) (by omega), hXctx, List.length_replicate,
            selLen_eq, ← (hans i x s).1, ← (hans i x s).2, encodeLog_append_single, hcodec,
            bitCodec_encodeEntry]
        obtain ⟨a, s', hsim, hraw⟩ := ih (hist ++ [⟨i, x, (ans i x s).1⟩]) (ans i x s).2 (t + 1)
          (by omega) hlen' (runsTo_succ hrun hnext (hbound _ _ _ hlen' (by omega)))
        refine ⟨a, s', ?_, hraw⟩
        rw [buildComp_succ_of_query hm, simulate_query, OracleComp.pure_bind]
        exact hsim
  have hstart : hStart X = hState (codec.encodeLog []) (List.ofFn init) 0 := by
    rw [hStart_eq, hX, NUPPT.inAdvice_layout, pairSndD_pairEncode, hState_eq,
      MachineCodec.encodeLog_nil, List.replicate_zero]
  have h0 : RunsTo hStart (hAct A q dα din dout stateLen run advIn out) (hBound q din dout stateLen)
      X 0 (hState (codec.encodeLog []) (List.ofFn init) 0) := by
    rw [← hstart]
    exact runsTo_zero (by rw [hstart]; exact hbound [] init 0 rfl (Nat.zero_le _))
  obtain ⟨a, s, hsim, hraw⟩ := key (q.eval n) [] init 0 (Nat.zero_add _) rfl h0
  refine ⟨a, s, ?_, hraw⟩
  rw [toCompOn_eq_advNext]
  exact hsim

end Spec

end TCSlib.Cryptography.Games.EffFill

## ===== TCSlib/Cryptography/Games/Efficiency/Interactive.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Efficiency.Strings
import TCSlib.Cryptography.Asymptotic.ReductionSupport

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The replay machine of an interactive handler (efficiency fill, T2)

The raw function behind `Games.exists_interactiveHandlerMachine` (route note
`briefs/pass-shelat-ch5-8/design/S2b-efficiency.md`, §"T2"), over the raw ingredients of an
interactive handler. Its functional equation is in
`TCSlib.Cryptography.Games.Efficiency.InteractiveSpec`.

The machine is an oracle machine against the outer oracles. On the raw layout
`X = ⟨⟨⟨1^n, ⟨⟨z, O⟩, ω⟩⟩, ⟨α_A, s₀⟩⟩, r⟩`, where `O` is its own encoded outer log, it replays the
whole reduction in an activation loop (`EffFill.actLoop`), one activation per round, on the state
`⟨ph, ⟨L, ⟨s, ⟨1^b, ⟨cur, ⟨L', ⟨1^c, O'⟩⟩⟩⟩⟩⟩⟩` (`iSt`):
- the phase `ph`: `[]` the adversary, `[true]` a call of the handler, `[false]` the finalization;
- the adversary's encoded log `L`, the handler's state `s` and the adversary's remaining budget `b`;
- in a call, the pending inner query `cur = ⟨1^i, x⟩`; in the finalization, the adversary's output
  `cur = a`;
- the outer log `L'` of the current call or finalization, and its remaining budget `c`;
- the part `O'` of `O` not yet replayed.

A round of the adversary runs `A` and opens a call (a query within budget) or the finalization (an
output, or a query at budget `0` with the all-`false` output). A round of a call runs `run` on
`⟨ctx, ⟨s, ⟨cur, L'⟩⟩⟩`: its answer `⟨y, s'⟩` (or the joint default at budget `0`) appends the
entry to `L` and returns to the adversary; an outer query is answered by the next entry of `O'`,
or, if `O'` is exhausted, **is the machine's next move**. The finalization runs `finRun` the same
way and stops with its output.

## Main definitions

* `EffFill.iSt`: the state word; `EffFill.iAct`, `EffFill.iStart`, `EffFill.iRaw`: the round, the
  initial state and the raw function; `EffFill.iRounds`, `EffFill.iBound`: the bounds.

## Main results

* `EffFill.iRaw_poly`: the raw function is polynomial-time.
* `EffFill.iAct_adv_ret`, …, `EffFill.iAct_fin_ask`: the round on each kind of state.
* `EffFill.length_iSt_le`: the state bound.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §2.1 (closure of p.p.t. machines under efficient operations; for example the reductions of the
  proofs of Theorems 135.4 and 168.2).
-/

namespace TCSlib.Cryptography.Games.EffFill

open Complexity Turing

variable {k k' : ℕ}

/-! ### The state word -/

/-- The state word `⟨ph, ⟨L, ⟨s, ⟨bA, ⟨cur, ⟨L', ⟨c, O'⟩⟩⟩⟩⟩⟩⟩` of the replay machine. -/
def iSt (ph L s bA cur L' c O' : List Bool) : List Bool :=
  pairEncode ph (pairEncode L (pairEncode s (pairEncode bA (pairEncode cur
    (pairEncode L' (pairEncode c O'))))))

/-- The defining equation of `iSt`. -/
theorem iSt_eq (ph L s bA cur L' c O' : List Bool) :
    iSt ph L s bA cur L' c O' = pairEncode ph (pairEncode L (pairEncode s (pairEncode bA
      (pairEncode cur (pairEncode L' (pairEncode c O')))))) :=
  rfl

/-- The phase of a state word. -/
def gPh (S : List Bool) : List Bool := pairFstD S
/-- The adversary's log of a state word. -/
def gLin (S : List Bool) : List Bool := pairFstD (pairSndD S)
/-- The handler's state of a state word. -/
def gS (S : List Bool) : List Bool := pairFstD (pairSndD (pairSndD S))
/-- The adversary's remaining budget of a state word. -/
def gB (S : List Bool) : List Bool := pairFstD (pairSndD (pairSndD (pairSndD S)))
/-- The pending query or output of a state word. -/
def gCur (S : List Bool) : List Bool := pairFstD (pairSndD (pairSndD (pairSndD (pairSndD S))))
/-- The outer log of the current call or finalization. -/
def gLc (S : List Bool) : List Bool :=
  pairFstD (pairSndD (pairSndD (pairSndD (pairSndD (pairSndD S)))))
/-- The remaining budget of the current call or finalization. -/
def gC (S : List Bool) : List Bool :=
  pairFstD (pairSndD (pairSndD (pairSndD (pairSndD (pairSndD (pairSndD S))))))
/-- The part of the outer log not yet replayed. -/
def gO (S : List Bool) : List Bool :=
  pairSndD (pairSndD (pairSndD (pairSndD (pairSndD (pairSndD (pairSndD S))))))

/-- The projection gPh on every raw state word is its nested pair projection. -/
theorem gPh_eq (S : List Bool) : gPh S = pairFstD (S) :=
  rfl

/-- The projection gLin on every raw state word is its nested pair projection. -/
theorem gLin_eq (S : List Bool) : gLin S = pairFstD (pairSndD (S)) :=
  rfl

/-- The projection gS on every raw state word is its nested pair projection. -/
theorem gS_eq (S : List Bool) : gS S = pairFstD (pairSndD (pairSndD (S))) :=
  rfl

/-- The projection gB on every raw state word is its nested pair projection. -/
theorem gB_eq (S : List Bool) : gB S = pairFstD (pairSndD (pairSndD (pairSndD (S)))) :=
  rfl

/-- The projection gCur on every raw state word is its nested pair projection. -/
theorem gCur_eq (S : List Bool) : gCur S = pairFstD (pairSndD (pairSndD (pairSndD (pairSndD (S))))) :=
  rfl

/-- The projection gLc on every raw state word is its nested pair projection. -/
theorem gLc_eq (S : List Bool) : gLc S = pairFstD (pairSndD (pairSndD (pairSndD (pairSndD (pairSndD (S)))))) :=
  rfl

/-- The projection gC on every raw state word is its nested pair projection. -/
theorem gC_eq (S : List Bool) : gC S = pairFstD (pairSndD (pairSndD (pairSndD (pairSndD (pairSndD (pairSndD (S))))))) :=
  rfl

/-- The projection gO on every raw state word is its nested pair projection. -/
theorem gO_eq (S : List Bool) : gO S = pairSndD (pairSndD (pairSndD (pairSndD (pairSndD (pairSndD (pairSndD (S))))))) :=
  rfl

section Read

variable (ph L s bA cur L' c O' : List Bool)

/-- `gPh (iSt ph …) = ph`. -/
theorem gPh_iSt : gPh (iSt ph L s bA cur L' c O') = ph := by
  simp only [gPh, iSt_eq, pairFstD_pairEncode]
/-- `gLin (iSt ph L …) = L`. -/
theorem gLin_iSt : gLin (iSt ph L s bA cur L' c O') = L := by
  simp only [gLin, iSt_eq, pairFstD_pairEncode, pairSndD_pairEncode]
/-- `gS (iSt ph L s …) = s`. -/
theorem gS_iSt : gS (iSt ph L s bA cur L' c O') = s := by
  simp only [gS, iSt_eq, pairFstD_pairEncode, pairSndD_pairEncode]
/-- `gB (iSt … bA …) = bA`. -/
theorem gB_iSt : gB (iSt ph L s bA cur L' c O') = bA := by
  simp only [gB, iSt_eq, pairFstD_pairEncode, pairSndD_pairEncode]
/-- `gCur (iSt … cur …) = cur`. -/
theorem gCur_iSt : gCur (iSt ph L s bA cur L' c O') = cur := by
  simp only [gCur, iSt_eq, pairFstD_pairEncode, pairSndD_pairEncode]
/-- `gLc (iSt … L' …) = L'`. -/
theorem gLc_iSt : gLc (iSt ph L s bA cur L' c O') = L' := by
  simp only [gLc, iSt_eq, pairFstD_pairEncode, pairSndD_pairEncode]
/-- `gC (iSt … c O') = c`. -/
theorem gC_iSt : gC (iSt ph L s bA cur L' c O') = c := by
  simp only [gC, iSt_eq, pairFstD_pairEncode, pairSndD_pairEncode]
/-- `gO (iSt … O') = O'`. -/
theorem gO_iSt : gO (iSt ph L s bA cur L' c O') = O' := by
  simp only [gO, iSt_eq, pairSndD_pairEncode]

end Read

/-- The context `⟨1^n, ⟨z, ω⟩⟩` read off the raw layout `⟨⟨⟨1^n, ⟨⟨z, O⟩, ω⟩⟩, α⟩, r⟩`. -/
def iCtx (X : List Bool) : List Bool :=
  pairEncode (NUPPT.inParam X)
    (pairEncode (pairFstD (pairFstD (NUPPT.inArg X))) (pairSndD (NUPPT.inArg X)))

/-- The defining equation of `iCtx`. -/
theorem iCtx_eq (X : List Bool) : iCtx X = pairEncode (NUPPT.inParam X)
    (pairEncode (pairFstD (pairFstD (NUPPT.inArg X))) (pairSndD (NUPPT.inArg X))) :=
  rfl

/-- The machine's own outer log `O`, read off the raw layout. -/
def iOuter (X : List Bool) : List Bool := pairSndD (pairFstD (NUPPT.inArg X))

/-- `iOuter X = snd (fst (inArg X))`. -/
theorem iOuter_eq (X : List Bool) : iOuter X = pairSndD (pairFstD (NUPPT.inArg X)) := rfl

/-! ### The rounds -/

section Raw

variable (A : NUPPT) (q dα : PolyExpr) (din dout : Fin k → PolyExpr) (din' : Fin k' → PolyExpr)
  (stateLen perCall outLen finCall : PolyExpr) (run advIn finRun : List Bool → List Bool)

/-- The adversary's canonical move word in a round of the adversary phase. -/
def iAdvMove (w : List Bool) : List Bool :=
  canonFun din (pairEncode (NUPPT.inParam (pairFstD w))
    (pairEncode (List.replicate (dα.eval (NUPPT.inParam (pairFstD w)).length) true)
      (A.output (NUPPT.layout (NUPPT.inParam (pairFstD w))
        (pairEncode (advIn (iCtx (pairFstD w))) (gLin (pairSndD w)))
        (pairFstD (NUPPT.inAdvice (pairFstD w))) (NUPPT.inCoins (pairFstD w))))))

/-- The defining equation of `iAdvMove`. -/
theorem iAdvMove_eq (w : List Bool) :
    iAdvMove A dα din advIn w =
      canonFun din (pairEncode (NUPPT.inParam (pairFstD w))
        (pairEncode (List.replicate (dα.eval (NUPPT.inParam (pairFstD w)).length) true)
          (A.output (NUPPT.layout (NUPPT.inParam (pairFstD w))
            (pairEncode (advIn (iCtx (pairFstD w))) (gLin (pairSndD w)))
            (pairFstD (NUPPT.inAdvice (pairFstD w))) (NUPPT.inCoins (pairFstD w)))))) :=
  rfl

/-- **A round of the adversary:** an output `a` opens the finalization with `cur = a`; a query at
budget `0` opens it with `0^{dα(n)}`; a query within budget opens a call with `cur = ⟨1^i, x⟩`. -/
def iAdvAct (w : List Bool) : List Bool :=
  if pairFstD (iAdvMove A dα din advIn w) = [true] then
    pairEncode [false] (iSt [false] (gLin (pairSndD w)) (gS (pairSndD w)) (gB (pairSndD w))
      (pairSndD (iAdvMove A dα din advIn w)) []
      (List.replicate (finCall.eval (NUPPT.inParam (pairFstD w)).length) true) (gO (pairSndD w)))
  else if gB (pairSndD w) = [] then
    pairEncode [false] (iSt [false] (gLin (pairSndD w)) (gS (pairSndD w)) (gB (pairSndD w))
      (List.replicate (dα.eval (NUPPT.inParam (pairFstD w)).length) false) []
      (List.replicate (finCall.eval (NUPPT.inParam (pairFstD w)).length) true) (gO (pairSndD w)))
  else
    pairEncode [false] (iSt [true] (gLin (pairSndD w)) (gS (pairSndD w)) ((gB (pairSndD w)).drop 1)
      (pairSndD (iAdvMove A dα din advIn w)) []
      (List.replicate (perCall.eval (NUPPT.inParam (pairFstD w)).length) true) (gO (pairSndD w)))

/-- The defining equation of `iAdvAct`. -/
theorem iAdvAct_eq (w : List Bool) :
    iAdvAct A dα din perCall finCall advIn w =
      if pairFstD (iAdvMove A dα din advIn w) = [true] then
        pairEncode [false] (iSt [false] (gLin (pairSndD w)) (gS (pairSndD w)) (gB (pairSndD w))
          (pairSndD (iAdvMove A dα din advIn w)) []
          (List.replicate (finCall.eval (NUPPT.inParam (pairFstD w)).length) true)
          (gO (pairSndD w)))
      else if gB (pairSndD w) = [] then
        pairEncode [false] (iSt [false] (gLin (pairSndD w)) (gS (pairSndD w)) (gB (pairSndD w))
          (List.replicate (dα.eval (NUPPT.inParam (pairFstD w)).length) false) []
          (List.replicate (finCall.eval (NUPPT.inParam (pairFstD w)).length) true)
          (gO (pairSndD w)))
      else
        pairEncode [false] (iSt [true] (gLin (pairSndD w)) (gS (pairSndD w))
          ((gB (pairSndD w)).drop 1) (pairSndD (iAdvMove A dα din advIn w)) []
          (List.replicate (perCall.eval (NUPPT.inParam (pairFstD w)).length) true)
          (gO (pairSndD w))) :=
  rfl

/-- The length `dout i (n)` of the answer to the pending query `cur = ⟨1^i, x⟩`. -/
def iAnsLen (w : List Bool) : ℕ :=
  selLen dout (NUPPT.inParam (pairFstD w)).length (pairFstD (gCur (pairSndD w))).length

/-- `iAnsLen w = selLen dout n |fst cur|`. -/
theorem iAnsLen_eq (w : List Bool) : iAnsLen dout w =
    selLen dout (NUPPT.inParam (pairFstD w)).length (pairFstD (gCur (pairSndD w))).length :=
  rfl

/-- The handler's canonical move word in a round of a call (result length `dout i + stateLen`). -/
def iCallMove (w : List Bool) : List Bool :=
  canonFun din' (pairEncode (NUPPT.inParam (pairFstD w))
    (pairEncode (List.replicate (iAnsLen dout w + stateLen.eval (NUPPT.inParam (pairFstD w)).length)
      true)
      (run (pairEncode (iCtx (pairFstD w)) (pairEncode (gS (pairSndD w))
        (pairEncode (gCur (pairSndD w)) (gLc (pairSndD w))))))))

/-- The defining equation of `iCallMove`. -/
theorem iCallMove_eq (w : List Bool) :
    iCallMove dout din' stateLen run w =
      canonFun din' (pairEncode (NUPPT.inParam (pairFstD w))
        (pairEncode (List.replicate (iAnsLen dout w +
            stateLen.eval (NUPPT.inParam (pairFstD w)).length) true)
          (run (pairEncode (iCtx (pairFstD w)) (pairEncode (gS (pairSndD w))
            (pairEncode (gCur (pairSndD w)) (gLc (pairSndD w)))))))) :=
  rfl

/-- The end of a call with result `W = y ‖ s'`: the entry `⟨1^i, ⟨x, y⟩⟩` is appended to the
adversary's log, the state becomes `s'`, and the phase returns to the adversary. -/
def iCallEnd (w W : List Bool) : List Bool :=
  iSt [] (gLin (pairSndD w) ++ pairEncode (pairEncode (pairFstD (gCur (pairSndD w)))
      (pairEncode (pairSndD (gCur (pairSndD w))) (W.take (iAnsLen dout w)))) [])
    (W.drop (iAnsLen dout w)) (gB (pairSndD w)) [] [] [] (gO (pairSndD w))

/-- The defining equation of `iCallEnd`. -/
theorem iCallEnd_eq (w W : List Bool) :
    iCallEnd dout w W =
      iSt [] (gLin (pairSndD w) ++ pairEncode (pairEncode (pairFstD (gCur (pairSndD w)))
          (pairEncode (pairSndD (gCur (pairSndD w))) (W.take (iAnsLen dout w)))) [])
        (W.drop (iAnsLen dout w)) (gB (pairSndD w)) [] [] [] (gO (pairSndD w)) :=
  rfl

/-- An outer query answered from the replayed log: the next entry of `O'` is appended to the
current outer log, its budget decreases, and the phase `ph` continues. -/
def iAsk (ph w : List Bool) : List Bool :=
  iSt ph (gLin (pairSndD w)) (gS (pairSndD w)) (gB (pairSndD w)) (gCur (pairSndD w))
    (gLc (pairSndD w) ++ pairEncode (pairFstD (gO (pairSndD w))) []) ((gC (pairSndD w)).drop 1)
    (pairSndD (gO (pairSndD w)))

/-- The defining equation of `iAsk`. -/
theorem iAsk_eq (ph w : List Bool) :
    iAsk ph w = iSt ph (gLin (pairSndD w)) (gS (pairSndD w)) (gB (pairSndD w)) (gCur (pairSndD w))
      (gLc (pairSndD w) ++ pairEncode (pairFstD (gO (pairSndD w))) []) ((gC (pairSndD w)).drop 1)
      (pairSndD (gO (pairSndD w))) :=
  rfl

/-- **A round of a call:** an answer ends the call; a query at budget `0` ends it with the joint
all-`false` default; a query within budget is answered from the replayed log or, when that is
exhausted, is the machine's move. -/
def iCallAct (w : List Bool) : List Bool :=
  if pairFstD (iCallMove dout din' stateLen run w) = [true] then
    pairEncode [false] (iCallEnd dout w (pairSndD (iCallMove dout din' stateLen run w)))
  else if gC (pairSndD w) = [] then
    pairEncode [false] (iCallEnd dout w (List.replicate
      (iAnsLen dout w + stateLen.eval (NUPPT.inParam (pairFstD w)).length) false))
  else if gO (pairSndD w) = [] then pairEncode [true] (iCallMove dout din' stateLen run w)
  else pairEncode [false] (iAsk [true] w)

/-- The defining equation of `iCallAct`. -/
theorem iCallAct_eq (w : List Bool) :
    iCallAct dout din' stateLen run w =
      if pairFstD (iCallMove dout din' stateLen run w) = [true] then
        pairEncode [false] (iCallEnd dout w (pairSndD (iCallMove dout din' stateLen run w)))
      else if gC (pairSndD w) = [] then
        pairEncode [false] (iCallEnd dout w (List.replicate
          (iAnsLen dout w + stateLen.eval (NUPPT.inParam (pairFstD w)).length) false))
      else if gO (pairSndD w) = [] then pairEncode [true] (iCallMove dout din' stateLen run w)
      else pairEncode [false] (iAsk [true] w) :=
  rfl

/-- The finalization's canonical move word in a round of the finalization. -/
def iFinMove (w : List Bool) : List Bool :=
  canonFun din' (pairEncode (NUPPT.inParam (pairFstD w))
    (pairEncode (List.replicate (outLen.eval (NUPPT.inParam (pairFstD w)).length) true)
      (finRun (pairEncode (iCtx (pairFstD w)) (pairEncode (gS (pairSndD w))
        (pairEncode (gCur (pairSndD w)) (gLc (pairSndD w))))))))

/-- The defining equation of `iFinMove`. -/
theorem iFinMove_eq (w : List Bool) :
    iFinMove din' outLen finRun w =
      canonFun din' (pairEncode (NUPPT.inParam (pairFstD w))
        (pairEncode (List.replicate (outLen.eval (NUPPT.inParam (pairFstD w)).length) true)
          (finRun (pairEncode (iCtx (pairFstD w)) (pairEncode (gS (pairSndD w))
            (pairEncode (gCur (pairSndD w)) (gLc (pairSndD w)))))))) :=
  rfl

/-- **A round of the finalization:** an output stops with its word; a query at budget `0` stops
with `⟨[true], 0^{outLen(n)}⟩`; a query within budget is answered from the replayed log or, when
that is exhausted, is the machine's move. -/
def iFinAct (w : List Bool) : List Bool :=
  if pairFstD (iFinMove din' outLen finRun w) = [true] then
    pairEncode [true] (iFinMove din' outLen finRun w)
  else if gC (pairSndD w) = [] then
    pairEncode [true] (pairEncode [true]
      (List.replicate (outLen.eval (NUPPT.inParam (pairFstD w)).length) false))
  else if gO (pairSndD w) = [] then pairEncode [true] (iFinMove din' outLen finRun w)
  else pairEncode [false] (iAsk [false] w)

/-- The defining equation of `iFinAct`. -/
theorem iFinAct_eq (w : List Bool) :
    iFinAct din' outLen finRun w =
      if pairFstD (iFinMove din' outLen finRun w) = [true] then
        pairEncode [true] (iFinMove din' outLen finRun w)
      else if gC (pairSndD w) = [] then
        pairEncode [true] (pairEncode [true]
          (List.replicate (outLen.eval (NUPPT.inParam (pairFstD w)).length) false))
      else if gO (pairSndD w) = [] then pairEncode [true] (iFinMove din' outLen finRun w)
      else pairEncode [false] (iAsk [false] w) :=
  rfl

/-- **One round of the replay machine**, by phase. -/
def iAct (w : List Bool) : List Bool :=
  if gPh (pairSndD w) = [] then iAdvAct A dα din perCall finCall advIn w
  else if gPh (pairSndD w) = [true] then iCallAct dout din' stateLen run w
  else iFinAct din' outLen finRun w

/-- The defining equation of `iAct`. -/
theorem iAct_eq (w : List Bool) :
    iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun w =
      if gPh (pairSndD w) = [] then iAdvAct A dα din perCall finCall advIn w
      else if gPh (pairSndD w) = [true] then iCallAct dout din' stateLen run w
      else iFinAct din' outLen finRun w :=
  rfl

/-- The initial state: the adversary's phase, empty log, the initial state `s₀` read off the
advice, the budget `1^{q(n)}`, and the whole outer log `O` still to replay. -/
def iStart (X : List Bool) : List Bool :=
  iSt [] [] (pairSndD (NUPPT.inAdvice X)) (List.replicate (q.eval (NUPPT.inParam X).length) true)
    [] [] [] (iOuter X)

/-- The defining equation of `iStart`. -/
theorem iStart_eq (X : List Bool) :
    iStart q X = iSt [] [] (pairSndD (NUPPT.inAdvice X))
      (List.replicate (q.eval (NUPPT.inParam X).length) true) [] [] [] (iOuter X) :=
  rfl

/-- The round bound `2 + finCall + q (perCall + 2)`: at most `q + 1` rounds of the adversary,
`perCall + 1` rounds per call and `finCall + 1` rounds of the finalization. -/
def iRounds : PolyExpr := .add (.add (.const 2) finCall) (.mul q (.add perCall (.const 2)))

/-- The defining equation of `iRounds`. -/
theorem iRounds_eq : iRounds q perCall finCall =
    .add (.add (.const 2) finCall) (.mul q (.add perCall (.const 2))) :=
  rfl

/-- The bound on the pending query or output: `2k + 2 + 2 Σ din + dα`. -/
def iCurBound : PolyExpr := .add (.const (2 * k + 2)) (.add (.mul (.const 2) (sumPoly din)) dα)

/-- The defining equation of `iCurBound`. -/
theorem iCurBound_eq : iCurBound dα din =
    .add (.const (2 * k + 2)) (.add (.mul (.const 2) (sumPoly din)) dα) :=
  rfl

/-- The fixed-length part of the state bound:
`16 + 2 (q E + stateLen + q + cur + (perCall + finCall)(E' + 1))`, with the entry bounds `E`, `E'`
of the inner and outer logs and the bound `cur` on the pending query or output. -/
def iFixBound (dout' : Fin k' → PolyExpr) : PolyExpr :=
  .add (.const 16) (.mul (.const 2) (.add (.mul q (entryPoly din dout)) (.add stateLen (.add q
    (.add (iCurBound dα din) (.mul (.add perCall finCall) (.add (entryPoly din' dout') (.const
        1))))))))

/-- The defining equation of `iFixBound`. -/
theorem iFixBound_eq (dout' : Fin k' → PolyExpr) :
    iFixBound q dα din dout din' stateLen perCall finCall dout' =
      .add (.const 16) (.mul (.const 2) (.add (.mul q (entryPoly din dout)) (.add stateLen (.add q
        (.add (iCurBound dα din)
          (.mul (.add perCall finCall) (.add (entryPoly din' dout') (.const 1)))))))) :=
  rfl

/-- The state bound: the fixed-length part plus `|X|` for the part of the outer log not yet
replayed. -/
def iBound (dout' : Fin k' → PolyExpr) : PolyExpr :=
  .add (iFixBound q dα din dout din' stateLen perCall finCall dout') .var

/-- `iBound = iFixBound + var`. -/
theorem iBound_eq (dout' : Fin k' → PolyExpr) :
    iBound q dα din dout din' stateLen perCall finCall dout' =
      .add (iFixBound q dα din dout din' stateLen perCall finCall dout') .var :=
  rfl

/-- **The raw function of the replay machine:** the activation loop of `iAct` from `iStart`. -/
def iRaw (dout' : Fin k' → PolyExpr) : List Bool → List Bool :=
  actLoop (iStart q) (iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun)
    (iRounds q perCall finCall) (iBound q dα din dout din' stateLen perCall finCall dout')

/-- `iRaw = actLoop iStart iAct iRounds iBound`. -/
theorem iRaw_eq (dout' : Fin k' → PolyExpr) :
    iRaw A q dα din dout din' stateLen perCall outLen finCall run advIn finRun dout' =
      actLoop (iStart q) (iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun)
        (iRounds q perCall finCall) (iBound q dα din dout din' stateLen perCall finCall dout') :=
  rfl

/-! ### Polynomial time -/

variable {run advIn finRun}

/-- The state word of polynomial-time components is polynomial-time. -/
theorem iSt_poly {f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ : List Bool → List Bool} (h₁ : PolyTimeComputable f₁)
    (h₂ : PolyTimeComputable f₂) (h₃ : PolyTimeComputable f₃) (h₄ : PolyTimeComputable f₄)
    (h₅ : PolyTimeComputable f₅) (h₆ : PolyTimeComputable f₆) (h₇ : PolyTimeComputable f₇)
    (h₈ : PolyTimeComputable f₈) :
    PolyTimeComputable fun w => iSt (f₁ w) (f₂ w) (f₃ w) (f₄ w) (f₅ w) (f₆ w) (f₇ w) (f₈ w) :=
  (h₁.pairEncode (h₂.pairEncode (h₃.pairEncode (h₄.pairEncode (h₅.pairEncode
    (h₆.pairEncode (h₇.pairEncode h₈))))))).congr fun _ => (iSt_eq _ _ _ _ _ _ _ _).symm

/-- The components of the state word of `w = ⟨X, S⟩` are polynomial-time in `w`. -/
theorem gS_comps_poly :
    PolyTimeComputable (fun w => gPh (pairSndD w)) ∧ PolyTimeComputable (fun w => gLin (pairSndD w))
        ∧
    PolyTimeComputable (fun w => gS (pairSndD w)) ∧ PolyTimeComputable (fun w => gB (pairSndD w)) ∧
    PolyTimeComputable (fun w => gCur (pairSndD w)) ∧ PolyTimeComputable (fun w => gLc (pairSndD w))
        ∧
    PolyTimeComputable (fun w => gC (pairSndD w)) ∧ PolyTimeComputable (fun w => gO (pairSndD w)) :=
        by
  have f := polyTimeComputable_pairFstD
  have g := polyTimeComputable_pairSndD
  refine ⟨f.comp' g, f.comp' (g.comp' g), f.comp' (g.comp' (g.comp' g)),
    f.comp' (g.comp' (g.comp' (g.comp' g))), f.comp' (g.comp' (g.comp' (g.comp' (g.comp' g)))),
    f.comp' (g.comp' (g.comp' (g.comp' (g.comp' (g.comp' g))))),
    f.comp' (g.comp' (g.comp' (g.comp' (g.comp' (g.comp' (g.comp' g)))))),
    g.comp' (g.comp' (g.comp' (g.comp' (g.comp' (g.comp' (g.comp' g))))))⟩

/-- The context is polynomial-time. -/
theorem iCtx_poly : PolyTimeComputable iCtx :=
  NUPPT.polyTimeComputable_inParam.pairEncode
    ((polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairFstD.comp'
      NUPPT.polyTimeComputable_inArg)).pairEncode
      (polyTimeComputable_pairSndD.comp' NUPPT.polyTimeComputable_inArg))

/-- The adversary's move word is polynomial-time. -/
theorem iAdvMove_poly (hadvIn : PolyTimeComputable advIn) :
    PolyTimeComputable (iAdvMove A dα din advIn) := by
  have hX := polyTimeComputable_pairFstD
  have hu := NUPPT.polyTimeComputable_inParam.comp' hX
  have hout := A.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout hu
    ((hadvIn.comp' (iCtx_poly.comp' hX)).pairEncode gS_comps_poly.2.1)
    (polyTimeComputable_pairFstD.comp' (NUPPT.polyTimeComputable_inAdvice.comp' hX))
    (NUPPT.polyTimeComputable_inCoins.comp' hX))
  exact (canonFun_poly din).comp' (hu.pairEncode ((StateLoop.unaryPoly_comp dα hu).pairEncode hout))

/-- A round of the adversary is polynomial-time. -/
theorem iAdvAct_poly (hadvIn : PolyTimeComputable advIn) :
    PolyTimeComputable (iAdvAct A dα din perCall finCall advIn) := by
  obtain ⟨-, hL, hs, hb, -, -, -, hO⟩ := gS_comps_poly
  have hu := NUPPT.polyTimeComputable_inParam.comp' polyTimeComputable_pairFstD
  have hm := iAdvMove_poly A dα din hadvIn
  have hfin := StateLoop.unaryPoly_comp finCall hu
  have hz : PolyTimeComputable fun w =>
      List.replicate (dα.eval (NUPPT.inParam (pairFstD w)).length) false :=
    (zeros_poly (StateLoop.unaryPoly_comp dα hu)).congr fun w => by rw [List.length_replicate]
  have h := polyTimeComputable_ite (eq_poly (polyTimeComputable_pairFstD.comp' hm)
      (polyTimeComputable_const [true]))
    ((polyTimeComputable_const [false]).pairEncode (iSt_poly (polyTimeComputable_const [false]) hL
        hs
      hb (polyTimeComputable_pairSndD.comp' hm) (polyTimeComputable_const []) hfin hO))
    (polyTimeComputable_ite (polyTimeComputable_isNil.comp' hb)
      ((polyTimeComputable_const [false]).pairEncode (iSt_poly (polyTimeComputable_const [false])
        hL hs hb hz (polyTimeComputable_const []) hfin hO))
      ((polyTimeComputable_const [false]).pairEncode (iSt_poly (polyTimeComputable_const [true])
        hL hs (polyTimeComputable_tail.comp' hb) (polyTimeComputable_pairSndD.comp' hm)
        (polyTimeComputable_const []) (StateLoop.unaryPoly_comp perCall hu) hO)))
  refine h.congr fun w => ?_
  rw [iAdvAct_eq]
  simp only [decide_eq_true_eq]

/-- The answer length `dout i (n)`, in unary, is polynomial-time. -/
theorem iAnsLen_poly : PolyTimeComputable fun w => List.replicate (iAnsLen dout w) true :=
  ((selLen_poly dout).comp' ((NUPPT.polyTimeComputable_inParam.comp'
      polyTimeComputable_pairFstD).pairEncode
    (polyTimeComputable_pairFstD.comp' gS_comps_poly.2.2.2.2.1))).congr fun w => by
    rw [iAnsLen_eq, pairFstD_pairEncode, pairSndD_pairEncode]

/-- The result length `dout i (n) + stateLen(n)`, in unary, is polynomial-time. -/
theorem iResLen_poly : PolyTimeComputable fun w => List.replicate
    (iAnsLen dout w + stateLen.eval (NUPPT.inParam (pairFstD w)).length) true :=
  ((iAnsLen_poly dout).append (StateLoop.unaryPoly_comp stateLen
    (NUPPT.polyTimeComputable_inParam.comp' polyTimeComputable_pairFstD))).congr fun w => by
    rw [List.replicate_add]

/-- The handler's input `⟨ctx, ⟨s, ⟨cur, L'⟩⟩⟩` is polynomial-time. -/
theorem iHInput_poly : PolyTimeComputable fun w => pairEncode (iCtx (pairFstD w))
    (pairEncode (gS (pairSndD w)) (pairEncode (gCur (pairSndD w)) (gLc (pairSndD w)))) :=
  (iCtx_poly.comp' polyTimeComputable_pairFstD).pairEncode (gS_comps_poly.2.2.1.pairEncode
    (gS_comps_poly.2.2.2.2.1.pairEncode gS_comps_poly.2.2.2.2.2.1))

/-- The handler's move word in a call is polynomial-time. -/
theorem iCallMove_poly (hrun : PolyTimeComputable run) :
    PolyTimeComputable (iCallMove dout din' stateLen run) :=
  (canonFun_poly din').comp' ((NUPPT.polyTimeComputable_inParam.comp'
    polyTimeComputable_pairFstD).pairEncode ((iResLen_poly dout stateLen).pairEncode
      (hrun.comp' iHInput_poly)))

/-- The end of a call with a polynomial-time result is polynomial-time. -/
theorem iCallEnd_poly {W : List Bool → List Bool} (hW : PolyTimeComputable W) :
    PolyTimeComputable fun w => iCallEnd dout w (W w) := by
  obtain ⟨-, hL, -, hb, hcur, -, -, hO⟩ := gS_comps_poly
  have hdl := iAnsLen_poly dout
  have h := iSt_poly (polyTimeComputable_const []) (hL.append
      (((polyTimeComputable_pairFstD.comp' hcur).pairEncode
        ((polyTimeComputable_pairSndD.comp' hcur).pairEncode (takeLen_poly hdl hW))).pairEncode
        (polyTimeComputable_const [])))
    (dropLen_poly hdl hW) hb (polyTimeComputable_const []) (polyTimeComputable_const [])
    (polyTimeComputable_const []) hO
  refine h.congr fun w => ?_
  rw [iCallEnd_eq, List.length_replicate]

/-- Answering an outer query from the replayed log is polynomial-time. -/
theorem iAsk_poly (ph : List Bool) : PolyTimeComputable (iAsk ph) := by
  obtain ⟨-, hL, hs, hb, hcur, hLc, hc, hO⟩ := gS_comps_poly
  exact (iSt_poly (polyTimeComputable_const ph) hL hs hb hcur
    (hLc.append ((polyTimeComputable_pairFstD.comp' hO).pairEncode (polyTimeComputable_const [])))
    (polyTimeComputable_tail.comp' hc) (polyTimeComputable_pairSndD.comp' hO)).congr fun w =>
    (iAsk_eq ph w).symm

/-- A round of a call is polynomial-time. -/
theorem iCallAct_poly (hrun : PolyTimeComputable run) :
    PolyTimeComputable (iCallAct dout din' stateLen run) := by
  have hm := iCallMove_poly dout din' stateLen hrun
  have h := polyTimeComputable_ite (eq_poly (polyTimeComputable_pairFstD.comp' hm)
      (polyTimeComputable_const [true]))
    ((polyTimeComputable_const [false]).pairEncode
      (iCallEnd_poly dout (polyTimeComputable_pairSndD.comp' hm)))
    (polyTimeComputable_ite (polyTimeComputable_isNil.comp' gS_comps_poly.2.2.2.2.2.2.1)
      ((polyTimeComputable_const [false]).pairEncode
        (iCallEnd_poly dout ((zeros_poly (iResLen_poly dout stateLen)).congr fun w => by
          rw [List.length_replicate])))
      (polyTimeComputable_ite (polyTimeComputable_isNil.comp' gS_comps_poly.2.2.2.2.2.2.2)
        ((polyTimeComputable_const [true]).pairEncode hm)
        ((polyTimeComputable_const [false]).pairEncode (iAsk_poly [true]))))
  refine h.congr fun w => ?_
  rw [iCallAct_eq]
  simp only [decide_eq_true_eq]

/-- The finalization's move word is polynomial-time. -/
theorem iFinMove_poly (hfinRun : PolyTimeComputable finRun) :
    PolyTimeComputable (iFinMove din' outLen finRun) :=
  (canonFun_poly din').comp' ((NUPPT.polyTimeComputable_inParam.comp'
    polyTimeComputable_pairFstD).pairEncode ((StateLoop.unaryPoly_comp outLen
      (NUPPT.polyTimeComputable_inParam.comp' polyTimeComputable_pairFstD)).pairEncode
      (hfinRun.comp' iHInput_poly)))

/-- A round of the finalization is polynomial-time. -/
theorem iFinAct_poly (hfinRun : PolyTimeComputable finRun) :
    PolyTimeComputable (iFinAct din' outLen finRun) := by
  have hm := iFinMove_poly din' outLen hfinRun
  have hu := NUPPT.polyTimeComputable_inParam.comp' polyTimeComputable_pairFstD
  have hz : PolyTimeComputable fun w =>
      List.replicate (outLen.eval (NUPPT.inParam (pairFstD w)).length) false :=
    (zeros_poly (StateLoop.unaryPoly_comp outLen hu)).congr fun w => by rw [List.length_replicate]
  have h := polyTimeComputable_ite (eq_poly (polyTimeComputable_pairFstD.comp' hm)
      (polyTimeComputable_const [true]))
    ((polyTimeComputable_const [true]).pairEncode hm)
    (polyTimeComputable_ite (polyTimeComputable_isNil.comp' gS_comps_poly.2.2.2.2.2.2.1)
      ((polyTimeComputable_const [true]).pairEncode ((polyTimeComputable_const [true]).pairEncode
          hz))
      (polyTimeComputable_ite (polyTimeComputable_isNil.comp' gS_comps_poly.2.2.2.2.2.2.2)
        ((polyTimeComputable_const [true]).pairEncode hm)
        ((polyTimeComputable_const [false]).pairEncode (iAsk_poly [false]))))
  refine h.congr fun w => ?_
  rw [iFinAct_eq]
  simp only [decide_eq_true_eq]

/-- **One round of the replay machine is polynomial-time.** -/
theorem iAct_poly (hrun : PolyTimeComputable run) (hadvIn : PolyTimeComputable advIn)
    (hfinRun : PolyTimeComputable finRun) :
    PolyTimeComputable (iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun) :=
        by
  have hph := gS_comps_poly.1
  have h := polyTimeComputable_ite (polyTimeComputable_isNil.comp' hph)
    (iAdvAct_poly A dα din perCall finCall hadvIn)
    (polyTimeComputable_ite (eq_poly hph (polyTimeComputable_const [true]))
      (iCallAct_poly dout din' stateLen hrun) (iFinAct_poly din' outLen hfinRun))
  refine h.congr fun w => ?_
  rw [iAct_eq]
  simp only [decide_eq_true_eq]

/-- **The raw function of the replay machine is polynomial-time** (`actLoop_poly`). -/
theorem iRaw_poly (dout' : Fin k' → PolyExpr) (hrun : PolyTimeComputable run)
    (hadvIn : PolyTimeComputable advIn) (hfinRun : PolyTimeComputable finRun) :
    PolyTimeComputable (iRaw A q dα din dout din' stateLen perCall outLen finCall run advIn finRun
      dout') := by
  have hstart : PolyTimeComputable (iStart q) :=
    (iSt_poly (polyTimeComputable_const []) (polyTimeComputable_const [])
      (polyTimeComputable_pairSndD.comp' NUPPT.polyTimeComputable_inAdvice)
      (StateLoop.unaryPoly_comp q NUPPT.polyTimeComputable_inParam) (polyTimeComputable_const [])
      (polyTimeComputable_const []) (polyTimeComputable_const [])
      (polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairFstD.comp'
        NUPPT.polyTimeComputable_inArg))).congr fun X => (iStart_eq q X).symm
  exact actLoop_poly hstart (iAct_poly A dα din dout din' stateLen perCall outLen finCall hrun
    hadvIn hfinRun) _ _

end Raw

/-! ### The rounds on state words -/

section Rounds

variable (A : NUPPT) (q dα : PolyExpr) (din dout : Fin k → PolyExpr) (din' : Fin k' → PolyExpr)
  (stateLen perCall outLen finCall : PolyExpr) (run advIn finRun : List Bool → List Bool)
  {X : List Bool} {n : ℕ}

/-- The adversary's move word on a state word: the canonical decoder of `A`'s output on
`⟨advIn ctx, L⟩` with the advice and coins of the layout. -/
theorem iAdvMove_iSt (hXu : NUPPT.inParam X = List.replicate n true)
    (ph L s bA cur L' c O' : List Bool) :
    iAdvMove A dα din advIn (pairEncode X (iSt ph L s bA cur L' c O')) =
      canonWord din n (dα.eval n) (A.output (NUPPT.layout (List.replicate n true)
        (pairEncode (advIn (iCtx X)) L) (pairFstD (NUPPT.inAdvice X)) (NUPPT.inCoins X))) := by
  rw [iAdvMove_eq, pairFstD_pairEncode, pairSndD_pairEncode, gLin_iSt, hXu, List.length_replicate]
  exact canonFun_eq din n (dα.eval n) _

/-- **The adversary outputs:** the finalization opens with `cur = a` and budget `finCall(n)`. -/
theorem iAct_adv_ret (hXu : NUPPT.inParam X = List.replicate n true)
    {L s bA cur L' c O' a : List Bool}
    (hm : iAdvMove A dα din advIn (pairEncode X (iSt [] L s bA cur L' c O')) = pairEncode [true] a)
        :
    iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun
        (pairEncode X (iSt [] L s bA cur L' c O')) =
      pairEncode [false] (iSt [false] L s bA a [] (List.replicate (finCall.eval n) true) O') := by
  rw [iAct_eq, pairSndD_pairEncode, gPh_iSt, if_pos rfl, iAdvAct_eq, hm,
    if_pos (pairFstD_pairEncode _ _)]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, gLin_iSt, gS_iSt, gB_iSt, gO_iSt, hXu,
    List.length_replicate]

/-- **The adversary queries at budget `0`:** the finalization opens with `cur = 0^{dα(n)}`. -/
theorem iAct_adv_timeout (hXu : NUPPT.inParam X = List.replicate n true)
    {L s cur L' c O' m : List Bool}
    (hm : iAdvMove A dα din advIn (pairEncode X (iSt [] L s [] cur L' c O')) = pairEncode [false] m)
        :
    iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun
        (pairEncode X (iSt [] L s [] cur L' c O')) =
      pairEncode [false] (iSt [false] L s [] (List.replicate (dα.eval n) false) []
        (List.replicate (finCall.eval n) true) O') := by
  rw [iAct_eq, pairSndD_pairEncode, gPh_iSt, if_pos rfl, iAdvAct_eq, hm, pairFstD_pairEncode,
    if_neg (by decide)]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, gLin_iSt, gS_iSt, gB_iSt, gO_iSt, hXu,
    List.length_replicate, if_true]

/-- **The adversary queries within budget:** a call opens with `cur = m` (the query `⟨1^i, x⟩`),
an empty outer log and budget `perCall(n)`. -/
theorem iAct_adv_query (hXu : NUPPT.inParam X = List.replicate n true)
    {L s bA cur L' c O' m : List Bool}
    (hm : iAdvMove A dα din advIn (pairEncode X (iSt [] L s (true :: bA) cur L' c O')) =
      pairEncode [false] m) :
    iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun
        (pairEncode X (iSt [] L s (true :: bA) cur L' c O')) =
      pairEncode [false] (iSt [true] L s bA m [] (List.replicate (perCall.eval n) true) O') := by
  rw [iAct_eq, pairSndD_pairEncode, gPh_iSt, if_pos rfl, iAdvAct_eq, hm, pairFstD_pairEncode,
    if_neg (by decide), pairSndD_pairEncode, gB_iSt, if_neg (List.cons_ne_nil _ _)]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, gLin_iSt, gS_iSt, gO_iSt, hXu,
    List.length_replicate, List.drop_one, List.tail_cons]

/-- The handler's move word in a call on the pending query `⟨iw, xw⟩`: the canonical decoder, with
result length `selLen dout n |iw| + stateLen(n)`, of `run ⟨ctx, ⟨s, ⟨⟨iw, xw⟩, L'⟩⟩⟩`. -/
theorem iCallMove_iSt (hXu : NUPPT.inParam X = List.replicate n true)
    (ph L s bA iw xw L' c O' : List Bool) :
    iCallMove dout din' stateLen run (pairEncode X (iSt ph L s bA (pairEncode iw xw) L' c O')) =
      canonWord din' n (selLen dout n iw.length + stateLen.eval n)
        (run (pairEncode (iCtx X) (pairEncode s (pairEncode (pairEncode iw xw) L')))) := by
  rw [iCallMove_eq, iAnsLen_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, gS_iSt, gCur_iSt, gLc_iSt, hXu,
    List.length_replicate]
  exact canonFun_eq din' n _ _

/-- **A call ends** with the result `W`: the entry `⟨iw, ⟨xw, y⟩⟩` is appended to the adversary's
log and the state becomes `s'`, where `W = y ‖ s'` is cut at `dout i (n)`. Both the handler's answer
and the joint default end a call this way (`iAct_call_ret`, `iAct_call_timeout`). -/
theorem iCallEnd_iSt (hXu : NUPPT.inParam X = List.replicate n true)
    (ph L s bA iw xw L' c O' W : List Bool) :
    iCallEnd dout (pairEncode X (iSt ph L s bA (pairEncode iw xw) L' c O')) W =
      iSt [] (L ++ pairEncode (pairEncode iw (pairEncode xw
          (W.take (selLen dout n iw.length)))) [])
        (W.drop (selLen dout n iw.length)) bA [] [] [] O' := by
  rw [iCallEnd_eq, iAnsLen_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, gLin_iSt, gB_iSt, gCur_iSt, gO_iSt, hXu,
    List.length_replicate]

/-- **The handler answers:** the call ends with the answer word `W` (`iCallEnd_iSt`). -/
theorem iAct_call_ret {L s bA iw xw L' c O' W : List Bool}
    (hm : iCallMove dout din' stateLen run (pairEncode X (iSt [true] L s bA (pairEncode iw xw) L' c
        O')) =
      pairEncode [true] W) :
    iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun
        (pairEncode X (iSt [true] L s bA (pairEncode iw xw) L' c O')) =
      pairEncode [false] (iCallEnd dout (pairEncode X (iSt [true] L s bA (pairEncode iw xw) L' c
          O'))
        W) := by
  rw [iAct_eq, pairSndD_pairEncode, gPh_iSt, if_neg (by decide), if_pos rfl, iCallAct_eq, hm,
    if_pos (pairFstD_pairEncode _ _), pairSndD_pairEncode]

/-- **The handler queries at budget `0`:** the call ends with the joint all-`false` default. -/
theorem iAct_call_timeout (hXu : NUPPT.inParam X = List.replicate n true)
    {L s bA iw xw L' O' m : List Bool}
    (hm : iCallMove dout din' stateLen run (pairEncode X (iSt [true] L s bA (pairEncode iw xw) L' []
        O')) =
      pairEncode [false] m) :
    iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun
        (pairEncode X (iSt [true] L s bA (pairEncode iw xw) L' [] O')) =
      pairEncode [false] (iCallEnd dout (pairEncode X (iSt [true] L s bA (pairEncode iw xw) L' []
          O'))
        (List.replicate (selLen dout n iw.length + stateLen.eval n) false)) := by
  rw [iAct_eq, pairSndD_pairEncode, gPh_iSt, if_neg (by decide), if_pos rfl, iCallAct_eq, hm,
    pairFstD_pairEncode, if_neg (by decide), pairSndD_pairEncode, gC_iSt, if_pos rfl, iAnsLen_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, gCur_iSt, hXu, List.length_replicate]

/-- **The handler queries within budget and the replayed log is exhausted:** the machine stops,
and its move is the handler's query word. -/
theorem iAct_call_stop {L s bA iw xw L' c m : List Bool}
    (hm : iCallMove dout din' stateLen run
        (pairEncode X (iSt [true] L s bA (pairEncode iw xw) L' (true :: c) [])) = pairEncode [false]
            m) :
    iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun
        (pairEncode X (iSt [true] L s bA (pairEncode iw xw) L' (true :: c) [])) =
      pairEncode [true] (pairEncode [false] m) := by
  rw [iAct_eq, pairSndD_pairEncode, gPh_iSt, if_neg (by decide), if_pos rfl, iCallAct_eq, hm,
    pairFstD_pairEncode, if_neg (by decide), pairSndD_pairEncode, gC_iSt, if_neg (List.cons_ne_nil _
        _),
    gO_iSt, if_pos rfl]

/-- **The handler queries within budget and the replayed log has an entry `e`:** `e` is appended
to the call's outer log, and the budget decreases. -/
theorem iAct_call_ask {L s bA iw xw L' c e O' m : List Bool}
    (hm : iCallMove dout din' stateLen run
        (pairEncode X (iSt [true] L s bA (pairEncode iw xw) L' (true :: c) (pairEncode e O'))) =
      pairEncode [false] m) :
    iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun
        (pairEncode X (iSt [true] L s bA (pairEncode iw xw) L' (true :: c) (pairEncode e O'))) =
      pairEncode [false] (iSt [true] L s bA (pairEncode iw xw) (L' ++ pairEncode e []) c O') := by
  rw [iAct_eq, pairSndD_pairEncode, gPh_iSt, if_neg (by decide), if_pos rfl, iCallAct_eq, hm,
    pairFstD_pairEncode, if_neg (by decide), pairSndD_pairEncode, gC_iSt, if_neg (List.cons_ne_nil _
        _),
    gO_iSt, if_neg (pairEncode_ne_nil _ _), iAsk_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, gLin_iSt, gS_iSt, gB_iSt, gCur_iSt, gLc_iSt,
    gC_iSt, gO_iSt, List.drop_one, List.tail_cons]

/-- The finalization's move word on a state word: the canonical decoder, with result length
`outLen(n)`, of `finRun ⟨ctx, ⟨s, ⟨cur, L'⟩⟩⟩`. -/
theorem iFinMove_iSt (hXu : NUPPT.inParam X = List.replicate n true)
    (ph L s bA cur L' c O' : List Bool) :
    iFinMove din' outLen finRun (pairEncode X (iSt ph L s bA cur L' c O')) =
      canonWord din' n (outLen.eval n)
        (finRun (pairEncode (iCtx X) (pairEncode s (pairEncode cur L')))) := by
  rw [iFinMove_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, gS_iSt, gCur_iSt, gLc_iSt, hXu,
    List.length_replicate]
  exact canonFun_eq din' n _ _

/-- **The finalization outputs:** the machine stops with the output word. -/
theorem iAct_fin_ret {L s bA cur L' c O' W : List Bool}
    (hm : iFinMove din' outLen finRun (pairEncode X (iSt [false] L s bA cur L' c O')) =
      pairEncode [true] W) :
    iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun
        (pairEncode X (iSt [false] L s bA cur L' c O')) =
      pairEncode [true] (pairEncode [true] W) := by
  rw [iAct_eq, pairSndD_pairEncode, gPh_iSt, if_neg (by decide), if_neg (by decide), iFinAct_eq, hm,
    if_pos (pairFstD_pairEncode _ _)]

/-- **The finalization queries at budget `0`:** the machine stops with `⟨[true], 0^{outLen(n)}⟩`. -/
theorem iAct_fin_timeout (hXu : NUPPT.inParam X = List.replicate n true)
    {L s bA cur L' O' m : List Bool}
    (hm : iFinMove din' outLen finRun (pairEncode X (iSt [false] L s bA cur L' [] O')) =
      pairEncode [false] m) :
    iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun
        (pairEncode X (iSt [false] L s bA cur L' [] O')) =
      pairEncode [true] (pairEncode [true] (List.replicate (outLen.eval n) false)) := by
  rw [iAct_eq, pairSndD_pairEncode, gPh_iSt, if_neg (by decide), if_neg (by decide), iFinAct_eq, hm,
    pairFstD_pairEncode, if_neg (by decide), pairSndD_pairEncode, gC_iSt, if_pos rfl,
    pairFstD_pairEncode, hXu,
    List.length_replicate]

/-- **The finalization queries within budget and the replayed log is exhausted:** the machine
stops, and its move is the finalization's query word. -/
theorem iAct_fin_stop {L s bA cur L' c m : List Bool}
    (hm : iFinMove din' outLen finRun (pairEncode X (iSt [false] L s bA cur L' (true :: c) [])) =
      pairEncode [false] m) :
    iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun
        (pairEncode X (iSt [false] L s bA cur L' (true :: c) [])) =
      pairEncode [true] (pairEncode [false] m) := by
  rw [iAct_eq, pairSndD_pairEncode, gPh_iSt, if_neg (by decide), if_neg (by decide), iFinAct_eq, hm,
    pairFstD_pairEncode, if_neg (by decide), pairSndD_pairEncode, gC_iSt,
    if_neg (List.cons_ne_nil _ _), gO_iSt, if_pos rfl]

/-- **The finalization queries within budget and the replayed log has an entry `e`:** `e` is
appended to the finalization's outer log, and the budget decreases. -/
theorem iAct_fin_ask {L s bA cur L' c e O' m : List Bool}
    (hm : iFinMove din' outLen finRun
        (pairEncode X (iSt [false] L s bA cur L' (true :: c) (pairEncode e O'))) =
      pairEncode [false] m) :
    iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun
        (pairEncode X (iSt [false] L s bA cur L' (true :: c) (pairEncode e O'))) =
      pairEncode [false] (iSt [false] L s bA cur (L' ++ pairEncode e []) c O') := by
  rw [iAct_eq, pairSndD_pairEncode, gPh_iSt, if_neg (by decide), if_neg (by decide), iFinAct_eq, hm,
    pairFstD_pairEncode, if_neg (by decide), pairSndD_pairEncode, gC_iSt,
    if_neg (List.cons_ne_nil _ _), gO_iSt, if_neg (pairEncode_ne_nil _ _), iAsk_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, gLin_iSt, gS_iSt, gB_iSt, gCur_iSt, gLc_iSt,
    gC_iSt, gO_iSt, List.drop_one, List.tail_cons]

end Rounds

/-! ### The state bound -/

/-- **The state bound:** a state word whose components are within their bounds at parameter
`n ≤ |X|`, and whose unreplayed log is at most `|X|` long, is within `iBound` at `|X|`. -/
theorem length_iSt_le (q dα : PolyExpr) (din dout : Fin k → PolyExpr) (din' dout' : Fin k' →
    PolyExpr)
    (stateLen perCall finCall : PolyExpr) {n m : ℕ} (hn : n ≤ m) {ph L s bA cur L' c O' : List Bool}
    (hph : ph.length ≤ 1) (hL : L.length ≤ q.eval n * (entryPoly din dout).eval n)
    (hs : s.length ≤ stateLen.eval n) (hbA : bA.length ≤ q.eval n)
    (hcur : cur.length ≤ (iCurBound dα din).eval n)
    (hL' : L'.length ≤ (perCall.eval n + finCall.eval n) * (entryPoly din' dout').eval n)
    (hc : c.length ≤ perCall.eval n + finCall.eval n) (hO : O'.length ≤ m) :
    (iSt ph L s bA cur L' c O').length ≤
      (iBound q dα din dout din' stateLen perCall finCall dout').eval m := by
  have hmono := (iFixBound q dα din dout din' stateLen perCall finCall dout').eval_mono hn
  rw [iBound_eq, PolyExpr.eval_add, PolyExpr.eval_var]
  refine le_trans ?_ (Nat.add_le_add_right hmono m)
  rw [iSt_eq]
  simp only [length_pairEncode, iFixBound_eq, PolyExpr.eval_add, PolyExpr.eval_mul,
    PolyExpr.eval_const]
  have : L'.length + c.length ≤
      (perCall.eval n + finCall.eval n) * ((entryPoly din' dout').eval n + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  omega

end TCSlib.Cryptography.Games.EffFill

## ===== TCSlib/Cryptography/Games/Efficiency/InteractiveSpec.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Efficiency.Interactive
import TCSlib.Cryptography.Games.Efficiency.Handler
import TCSlib.Cryptography.Games.Efficiency.Replay

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The functional equation of the replay machine (efficiency fill, T2)

The replay machine of `TCSlib.Cryptography.Games.Efficiency.Interactive`, run as an oracle machine
against the outer oracles, **is** the reduction: its computation tree equals the simulation of the
adversary by the interactive handler followed by the finalization (`iRaw_spec`). Route note
`briefs/pass-shelat-ch5-8/design/S2b-efficiency.md`, §"T2", steps 4 and 5.

The proof shows that the machine's next-move function replays the reduction tree
(`EffFill.ReplaysFrom`), by three nested inductions along the phases of the reduction, the
finalization (`fin_phase`), a call (`call_phase`) and the adversary (`adv_phase`). The invariant
(`IInv`) says that, on every outer log extending the replayed prefix, the activation loop has
reached the state word encoding the current position. The tree makes at most
`q(n) · perCall(n) + finCall(n)` queries (`costBoundedBy_mul`, `simulate_costBoundedBy`), so the
machine's budget never cuts the replay short (`buildComp_of_replaysFrom`).

## Main definitions

* `EffFill.iCall`, `EffFill.iImpl`, `EffFill.iFinish`: one call of the handler, the handler as an
  implementation, and the finalization, over the raw ingredients.
* `EffFill.iX`: the raw layout on the outer log `O`; `EffFill.IInv`: the replay invariant.

## Main results

* `EffFill.iRaw_spec`: the machine's computation is the reduction.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §2.1 (closure of p.p.t. machines under efficient operations; for example the reductions of the
  proofs of Theorems 135.4 and 168.2).
-/

namespace TCSlib.Cryptography.Games.EffFill

open Complexity Turing

variable {k k' : ℕ}

/-- Cutting the string of a `(a + b)`-bit word at `a` gives its two parts:
`(ofFn w).take a = ofFn (w ∘ castAdd b)` and `(ofFn w).drop a = ofFn (w ∘ natAdd a)`. -/
theorem ofFn_take_drop_add {a b : ℕ} (w : Fin (a + b) → Bool) :
    (List.ofFn w).take a = List.ofFn (fun j => w (Fin.castAdd b j)) ∧
      (List.ofFn w).drop a = List.ofFn (fun j => w (Fin.natAdd a j)) := by
  rw [List.ofFn_add]
  exact ⟨List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn⟩

section Spec

variable (A : NUPPT) (q dα : PolyExpr) (din dout : Fin k → PolyExpr) (din' dout' : Fin k' →
    PolyExpr)
  (stateLen perCall outLen finCall : PolyExpr) (run advIn finRun : List Bool → List Bool)

/-- The next-move function of one call of the interactive handler on the inner query `x` to
oracle `i` in state `s`, at parameter `n` with the reduction's input `z` and seed `ω`: `run` on
`⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`, decoded with result length `dout i + stateLen`. -/
def iCallNext (n : ℕ) (z ω : List Bool) (s : Fin (stateLen.eval n) → Bool) (i : Fin k)
    (x : Fin ((din i).eval n) → Bool)
    (L : QueryLog (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n))) :
    Move (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n))
      (Fin ((dout i).eval n + stateLen.eval n) → Bool) :=
  decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
    ((dout i).eval n + stateLen.eval n)
    (run (pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
      (pairEncode (List.ofFn s) (pairEncode (pairEncode (List.replicate i true) (List.ofFn x))
        ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L)))))

/-- The defining equation of `iCallNext`. -/
theorem iCallNext_eq (n : ℕ) (z ω : List Bool) (s : Fin (stateLen.eval n) → Bool) (i : Fin k)
    (x : Fin ((din i).eval n) → Bool)
    (L : QueryLog (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n))) :
    iCallNext din dout din' dout' stateLen run n z ω s i x L =
      decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
        ((dout i).eval n + stateLen.eval n)
        (run (pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
          (pairEncode (List.ofFn s) (pairEncode (pairEncode (List.replicate i true) (List.ofFn x))
            ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))) :=
  rfl

/-- **One call** of the interactive handler: `buildComp` of `iCallNext` from the empty outer log
with budget `perCall(n)` and the joint all-`false` default (the term of
`InteractiveHandler.call`). -/
def iCall (n : ℕ) (z ω : List Bool) (s : Fin (stateLen.eval n) → Bool) (i : Fin k)
    (x : Fin ((din i).eval n) → Bool) :
    OracleComp (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n))
      (Fin ((dout i).eval n + stateLen.eval n) → Bool) :=
  buildComp (iCallNext din dout din' dout' stateLen run n z ω s i x) (zeroBits _) (perCall.eval n)
      []

/-- `iCall … = buildComp (iCallNext …) (zeroBits _) (perCall n) []`. -/
theorem iCall_eq_buildComp (n : ℕ) (z ω : List Bool) (s : Fin (stateLen.eval n) → Bool) (i : Fin k)
    (x : Fin ((din i).eval n) → Bool) :
    iCall din dout din' dout' stateLen perCall run n z ω s i x =
      buildComp (iCallNext din dout din' dout' stateLen run n z ω s i x) (zeroBits _)
        (perCall.eval n) [] :=
  rfl

/-- The defining equation of `iCall`, with the next-move function written out. -/
theorem iCall_eq (n : ℕ) (z ω : List Bool) (s : Fin (stateLen.eval n) → Bool) (i : Fin k)
    (x : Fin ((din i).eval n) → Bool) :
    iCall din dout din' dout' stateLen perCall run n z ω s i x =
      buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
          ((dout i).eval n + stateLen.eval n)
          (run (pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
            (pairEncode (List.ofFn s) (pairEncode (pairEncode (List.replicate i true) (List.ofFn x))
              ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))))
        (zeroBits _) (perCall.eval n) [] :=
  rfl

/-- **The handler as an implementation** of the inner oracles by the outer ones: one call per
inner query, its result split into the answer and the new state (the term of
`InteractiveHandler.impl`). -/
def iImpl (n : ℕ) (z ω : List Bool) :
    QueryImpl (bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n))
      (Fin (stateLen.eval n) → Bool) (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval
          n)) :=
  fun i x s => (iCall din dout din' dout' stateLen perCall run n z ω s i x).bind fun w =>
    .pure (fun j => w (Fin.castAdd (stateLen.eval n) j), fun j => w (Fin.natAdd ((dout i).eval n)
        j))

/-- The defining equation of `iImpl`. -/
theorem iImpl_apply (n : ℕ) (z ω : List Bool) (i : Fin k) (x : Fin ((din i).eval n) → Bool)
    (s : Fin (stateLen.eval n) → Bool) :
    iImpl din dout din' dout' stateLen perCall run n z ω i x s =
      (iCall din dout din' dout' stateLen perCall run n z ω s i x).bind fun w =>
        .pure (fun j => w (Fin.castAdd (stateLen.eval n) j), fun j => w (Fin.natAdd ((dout i).eval
            n) j)) :=
  rfl

/-- The next-move function of the finalization in state `s` after the adversary's output `a`:
`finRun` on `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨a, L⟩⟩⟩`, decoded with result length `outLen(n)`. -/
def iFinNext (n : ℕ) (z ω : List Bool) (s : Fin (stateLen.eval n) → Bool) {d : ℕ} (a : Fin d → Bool)
    (L : QueryLog (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n))) :
    Move (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n))
      (Fin (outLen.eval n) → Bool) :=
  decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n) (outLen.eval n)
    (finRun (pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
      (pairEncode (List.ofFn s) (pairEncode (List.ofFn a)
        ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L)))))

/-- The defining equation of `iFinNext`. -/
theorem iFinNext_eq (n : ℕ) (z ω : List Bool) (s : Fin (stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool)
    (L : QueryLog (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n))) :
    iFinNext din' dout' stateLen outLen finRun n z ω s a L =
      decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n) (outLen.eval n)
        (finRun (pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
          (pairEncode (List.ofFn s) (pairEncode (List.ofFn a)
            ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))) :=
  rfl

/-- **The finalization** in state `s` after the adversary's output `a`: `buildComp` of
`iFinNext` with budget `finCall(n)` (the term of `InteractiveHandler.finish`). -/
def iFinish (n : ℕ) (z ω : List Bool) (s : Fin (stateLen.eval n) → Bool) {d : ℕ} (a : Fin d → Bool)
    :
    OracleComp (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n))
      (Fin (outLen.eval n) → Bool) :=
  buildComp (iFinNext din' dout' stateLen outLen finRun n z ω s a) (zeroBits _) (finCall.eval n) []

/-- `iFinish … = buildComp (iFinNext …) (zeroBits _) (finCall n) []`. -/
theorem iFinish_eq_buildComp (n : ℕ) (z ω : List Bool) (s : Fin (stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool) :
    iFinish din' dout' stateLen outLen finCall finRun n z ω s a =
      buildComp (iFinNext din' dout' stateLen outLen finRun n z ω s a) (zeroBits _)
        (finCall.eval n) [] :=
  rfl

/-- The defining equation of `iFinish`, with the next-move function written out. -/
theorem iFinish_eq (n : ℕ) (z ω : List Bool) (s : Fin (stateLen.eval n) → Bool) {d : ℕ}
    (a : Fin d → Bool) :
    iFinish din' dout' stateLen outLen finCall finRun n z ω s a =
      buildComp (fun L => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
          (outLen.eval n)
          (finRun (pairEncode (pairEncode (List.replicate n true) (pairEncode z ω))
            (pairEncode (List.ofFn s) (pairEncode (List.ofFn a)
              ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) 0).encodeLog L))))))
        (zeroBits _) (finCall.eval n) [] :=
  rfl

/-- The raw layout of the machine on its outer log `O`:
`⟨⟨⟨1^n, ⟨⟨z, encodeLog O⟩, ω⟩⟩, ⟨A.advice n, s₀⟩⟩, r⟩`. -/
def iX (n : ℕ) (z ω : List Bool) (r : A.Coins n) (init : Fin (stateLen.eval n) → Bool)
    (O : QueryLog (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n))) : List Bool :=
  NUPPT.layout (List.replicate n true)
    (pairEncode (pairEncode z
      ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n) (outLen.eval n)).encodeLog
          O))
      ω)
    (pairEncode (A.advice n) (List.ofFn init)) (List.ofFn r)

/-- The defining equation of `iX`. -/
theorem iX_eq (n : ℕ) (z ω : List Bool) (r : A.Coins n) (init : Fin (stateLen.eval n) → Bool)
    (O : QueryLog (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n))) :
    iX A din' dout' stateLen outLen n z ω r init O =
      NUPPT.layout (List.replicate n true)
        (pairEncode (pairEncode z
          ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
            (outLen.eval n)).encodeLog O)) ω)
        (pairEncode (A.advice n) (List.ofFn init)) (List.ofFn r) :=
  rfl

/-- **The replay invariant:** on every outer log `P ++ O'` extending the replayed prefix `P`, the
activation loop has run `t` rounds without stopping, within the state bound, and reached the
state word `S O'`. -/
def IInv (n : ℕ) (z ω : List Bool) (r : A.Coins n) (init : Fin (stateLen.eval n) → Bool) (t : ℕ)
    (P : QueryLog (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n)))
    (S : QueryLog (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n)) → List Bool) :
    Prop :=
  ∀ O', RunsTo (iStart q) (iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun)
    (iBound q dα din dout din' stateLen perCall finCall dout')
    (iX A din' dout' stateLen outLen n z ω r init (P ++ O')) t (S O')

/-- `IInv … t P S ↔ ∀ O', RunsTo … (iX (P ++ O')) t (S O')`. -/
theorem iInv_iff (n : ℕ) (z ω : List Bool) (r : A.Coins n) (init : Fin (stateLen.eval n) → Bool)
    (t : ℕ) (P : QueryLog (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n)))
    (S : QueryLog (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n)) → List Bool) :
    IInv A q dα din dout din' dout' stateLen perCall outLen finCall run advIn finRun n z ω r init t
        P S ↔
      ∀ O', RunsTo (iStart q)
        (iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun)
        (iBound q dα din dout din' stateLen perCall finCall dout')
        (iX A din' dout' stateLen outLen n z ω r init (P ++ O')) t (S O') :=
  Iff.rfl

/-- The machine's next move on the outer log `O`: its output on the layout `iX O`, decoded with
the machine's codec. -/
def iNext (n : ℕ) (z ω : List Bool) (r : A.Coins n) (init : Fin (stateLen.eval n) → Bool)
    (O : QueryLog (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n))) :
    Move (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n))
      (Fin (outLen.eval n) → Bool) :=
  decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n) (outLen.eval n)
    (iRaw A q dα din dout din' stateLen perCall outLen finCall run advIn finRun dout'
      (iX A din' dout' stateLen outLen n z ω r init O))

/-- The defining equation of `iNext`. -/
theorem iNext_eq (n : ℕ) (z ω : List Bool) (r : A.Coins n) (init : Fin (stateLen.eval n) → Bool)
    (O : QueryLog (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n))) :
    iNext A q dα din dout din' dout' stateLen perCall outLen finCall run advIn finRun n z ω r init O
        =
      decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n) (outLen.eval n)
        (iRaw A q dα din dout din' stateLen perCall outLen finCall run advIn finRun dout'
          (iX A din' dout' stateLen outLen n z ω r init O)) :=
  rfl

/-- **The rest of the reduction** from an adversary's position: the simulation, by the handler from
state `s`, of the adversary's computation from its log `hist` with remaining budget `b`, followed
by the finalization. -/
def iTree (n : ℕ) (z ω : List Bool) (r : A.Coins n)
    (hist : QueryLog (bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n)))
    (s : Fin (stateLen.eval n) → Bool) (b : ℕ) :
    OracleComp (bitSpec (fun j => (din' j).eval n) (fun j => (dout' j).eval n))
      (Fin (outLen.eval n) → Bool) :=
  (simulate (iImpl din dout din' dout' stateLen perCall run n z ω)
    (buildComp (advNext A (bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval
        n))
      n (advIn (pairEncode (List.replicate n true) (pairEncode z ω))) r) (zeroBits _) b hist)
          s).bind
    fun res => iFinish din' dout' stateLen outLen finCall finRun n z ω res.2 res.1

/-- The defining equation of `iTree`. -/
theorem iTree_eq (n : ℕ) (z ω : List Bool) (r : A.Coins n)
    (hist : QueryLog (bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n)))
    (s : Fin (stateLen.eval n) → Bool) (b : ℕ) :
    iTree A dα din dout din' dout' stateLen perCall outLen finCall run advIn finRun n z ω r hist s b
        =
      (simulate (iImpl din dout din' dout' stateLen perCall run n z ω)
        (buildComp (advNext A (bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n)
          (dα.eval n)) n (advIn (pairEncode (List.replicate n true) (pairEncode z ω))) r)
          (zeroBits _) b hist) s).bind
        fun res => iFinish din' dout' stateLen outLen finCall finRun n z ω res.2 res.1 :=
  rfl

section Phases

variable {A q dα din dout din' dout' stateLen perCall outLen finCall run advIn finRun}
  {n : ℕ} {z ω : List Bool} {r : A.Coins n} {init : Fin (stateLen.eval n) → Bool}

local notation "INNER" => bitSpec (fun i => PolyExpr.eval (din i) n) (fun i => PolyExpr.eval (dout
    i) n)
local notation "OUTER" => bitSpec (fun j => PolyExpr.eval (din' j) n) (fun j => PolyExpr.eval (dout'
    j) n)
local notation "CIN" => bitCodec (fun i => PolyExpr.eval (din i) n) (fun i => PolyExpr.eval (dout i)
    n)
  (PolyExpr.eval dα n)
local notation "COUT" => bitCodec (fun j => PolyExpr.eval (din' j) n) (fun j => PolyExpr.eval (dout'
    j) n)
  (PolyExpr.eval outLen n)
local notation "XOF" => iX A din' dout' stateLen outLen n z ω r init
local notation "INV" => IInv A q dα din dout din' dout' stateLen perCall outLen finCall run advIn
  finRun n z ω r init
local notation "NEXT" => iNext A q dα din dout din' dout' stateLen perCall outLen finCall run advIn
  finRun n z ω r init
local notation "ACT" => iAct A dα din dout din' stateLen perCall outLen finCall run advIn finRun
local notation "BND" => iBound q dα din dout din' stateLen perCall finCall dout'
local notation "CTX" => pairEncode (List.replicate n true) (pairEncode z ω)
local notation "TREE" => iTree A dα din dout din' dout' stateLen perCall outLen finCall run advIn
  finRun n z ω r

/-- The parameter of the layout `iX O` is `1^n`. -/
theorem iX_inParam (O : QueryLog OUTER) : NUPPT.inParam (XOF O) = List.replicate n true := by
  rw [iX_eq, NUPPT.inParam_layout]

/-- The context read off the layout `iX O` is `⟨1^n, ⟨z, ω⟩⟩`. -/
theorem iX_ctx (O : QueryLog OUTER) : iCtx (XOF O) = CTX := by
  rw [iCtx_eq, iX_inParam, iX_eq, NUPPT.inArg_layout, pairFstD_pairEncode, pairFstD_pairEncode,
    pairSndD_pairEncode]

/-- The advice of the layout `iX O` is `⟨A.advice n, s₀⟩`. -/
theorem iX_inAdvice (O : QueryLog OUTER) :
    NUPPT.inAdvice (XOF O) = pairEncode (A.advice n) (List.ofFn init) := by
  rw [iX_eq, NUPPT.inAdvice_layout]

/-- The coins of the layout `iX O` are `A`'s coins `r`. -/
theorem iX_inCoins (O : QueryLog OUTER) : NUPPT.inCoins (XOF O) = List.ofFn r := by
  rw [iX_eq, NUPPT.inCoins_layout]

/-- The outer log read off the layout `iX O` is the encoding of `O`. -/
theorem iX_outer (O : QueryLog OUTER) : iOuter (XOF O) = (COUT).encodeLog O := by
  rw [iOuter_eq, iX_eq, NUPPT.inArg_layout, pairFstD_pairEncode, pairSndD_pairEncode]

/-- The parameter is at most the length of the layout. -/
theorem le_length_iX (O : QueryLog OUTER) : n ≤ (XOF O).length := by
  rw [iX_eq]
  exact le_length_layout n _ _ _

/-- The encoded outer log is at most the length of the layout. -/
theorem length_encodeLog_le_iX (O : QueryLog OUTER) : ((COUT).encodeLog O).length ≤ (XOF O).length
    := by
  rw [iX_eq, NUPPT.layout_eq]
  simp only [length_pairEncode]
  omega

/-- A continuing round on every extension preserves the invariant (`runsTo_succ`). -/
theorem iInv_succ {t : ℕ} {P : QueryLog OUTER} {S S' : QueryLog OUTER → List Bool} (h : INV t P S)
    (hact : ∀ O', ACT (pairEncode (XOF (P ++ O')) (S O')) = pairEncode [false] (S' O'))
    (hb : ∀ O', (S' O').length ≤ (BND).eval (XOF (P ++ O')).length) : INV (t + 1) P S' :=
  fun O' => runsTo_succ (h O') (hact O') (hb O')

/-- **Replaying an entry:** if, on every extension `e :: O'`, the round continues with the state
`S' O'` (the entry `e` consumed), the invariant holds one round later with `e` replayed. -/
theorem iInv_consume {t : ℕ} {P : QueryLog OUTER} {S S' : QueryLog OUTER → List Bool}
    (e : Σ j, (OUTER).dom j × (OUTER).rng j) (h : INV t P S)
    (hact : ∀ O', ACT (pairEncode (XOF (P ++ e :: O')) (S (e :: O'))) = pairEncode [false] (S' O'))
    (hb : ∀ O', (S' O').length ≤ (BND).eval (XOF ((P ++ [e]) ++ O')).length) :
    INV (t + 1) (P ++ [e]) S' := by
  intro O'
  have hO : (P ++ [e]) ++ O' = P ++ e :: O' := by rw [List.append_assoc, List.singleton_append]
  have hb' := hb O'
  rw [hO] at hb' ⊢
  exact runsTo_succ (h (e :: O')) (hact O') hb'

/-- **A stopping round** on the replayed prefix `P` itself is the machine's next move on `P`
(`runsTo_stop`). -/
theorem iInv_stop {t : ℕ} {P : QueryLog OUTER} {S : QueryLog OUTER → List Bool} {W : List Bool}
    (h : INV t P S) (hact : ACT (pairEncode (XOF P) (S [])) = pairEncode [true] W)
    (ht : t ≤ (iRounds q perCall finCall).eval n) :
    NEXT P = decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n) (outLen.eval n) W
        := by
  have h0 := h []
  rw [List.append_nil] at h0
  rw [iNext_eq, iRaw_eq, runsTo_stop h0 hact
    (ht.trans ((iRounds q perCall finCall).eval_mono (le_length_iX P)))]

/-- **The typed state bound:** a state word built from an inner log of at most `q(n)` entries, the
handler's state, a budget of at most `q(n)`, and components within their bounds, is within
`iBound` on every layout extending the replayed prefix. -/
theorem iSt_le_iBound (P O' : QueryLog OUTER) (ph cur Lc cw : List Bool) (hist : QueryLog INNER)
    (s : Fin (stateLen.eval n) → Bool) (b : ℕ) (hph : ph.length ≤ 1) (hhist : hist.length ≤ q.eval
        n)
    (hb : b ≤ q.eval n) (hcur : cur.length ≤ (iCurBound dα din).eval n)
    (hLc : Lc.length ≤ (perCall.eval n + finCall.eval n) * (entryPoly din' dout').eval n)
    (hcw : cw.length ≤ perCall.eval n + finCall.eval n) :
    (iSt ph ((CIN).encodeLog hist) (List.ofFn s) (List.replicate b true) cur Lc cw
      ((COUT).encodeLog O')).length ≤ (BND).eval (XOF (P ++ O')).length :=
  length_iSt_le q dα din dout din' dout' stateLen perCall finCall (le_length_iX _) hph
    ((length_encodeLog_le CIN _ hist (fun e _ => entry_le_entryPoly din dout n e _)).trans
      (Nat.mul_le_mul_right _ hhist))
    (by rw [List.length_ofFn]) (by rw [List.length_replicate]; exact hb) hcur hLc hcw
    ((length_encodeLog_le_append COUT O' P).trans (length_encodeLog_le_iX _))

/-- An outer log of at most `c` entries is at most `c · E'` bits. -/
theorem outLog_le (L : QueryLog OUTER) {c : ℕ} (hL : L.length ≤ c) :
    ((COUT).encodeLog L).length ≤ c * (entryPoly din' dout').eval n :=
  (length_encodeLog_le COUT _ L (fun e _ => entry_le_entryPoly din' dout' n e _)).trans
    (Nat.mul_le_mul_right _ hL)

/-- A pending inner query `⟨1^i, x⟩` is within the bound `iCurBound`. -/
theorem query_le_iCurBound (i : Fin k) (x : Fin ((din i).eval n) → Bool) :
    (pairEncode (List.replicate i true) (List.ofFn x)).length ≤ (iCurBound dα din).eval n := by
  rw [length_pairEncode, List.length_replicate, List.length_ofFn, iCurBound_eq]
  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
  have h1 := i.isLt
  have h2 := eval_le_sumPoly din i n
  omega

/-- An adversary's output is within the bound `iCurBound`. -/
theorem output_le_iCurBound (a : Fin (dα.eval n) → Bool) :
    (List.ofFn a).length ≤ (iCurBound dα din).eval n := by
  rw [List.length_ofFn, iCurBound_eq]
  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
  omega

/-- The adversary's move word on the layout `iX O` and a state word with log `hist` is the
canonical word of its next move (`canonWord_eq`). -/
theorem iAdvMove_iX (O : QueryLog OUTER) (hist : QueryLog INNER) (sw bw cur Lc cw Ow : List Bool) :
    iAdvMove A dα din advIn (pairEncode (XOF O) (iSt [] ((CIN).encodeLog hist) sw bw cur Lc cw Ow))
        =
      encodeBitMove (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n)
        (advNext A CIN n (advIn CTX) r hist) := by
  rw [iAdvMove_iSt A dα din advIn (iX_inParam O), iX_ctx, iX_inAdvice, iX_inCoins,
    pairFstD_pairEncode, ← NUPPT.runAtL_eq_output_layout, ← NUPPT.runAt_eq,
    canonWord_eq din (fun i => (dout i).eval n), advNext_eq, bitCodec_decodeMove]

/-- The handler's move word in a call on the layout `iX O` is the canonical word of the call's
next move (`canonWord_eq`, `encodeLog_bitCodec`). -/
theorem iCallMove_iX (O : QueryLog OUTER) (ph Lin : List Bool) (s : Fin (stateLen.eval n) → Bool)
    (bw : List Bool) (i : Fin k) (x : Fin ((din i).eval n) → Bool) (L : QueryLog OUTER)
    (cw Ow : List Bool) :
    iCallMove dout din' stateLen run (pairEncode (XOF O) (iSt ph Lin (List.ofFn s) bw
        (pairEncode (List.replicate i true) (List.ofFn x)) ((COUT).encodeLog L) cw Ow)) =
      encodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
        ((dout i).eval n + stateLen.eval n)
        (iCallNext din dout din' dout' stateLen run n z ω s i x L) := by
  rw [iCallMove_iSt dout din' stateLen run (iX_inParam O), iX_ctx, List.length_replicate, selLen_eq,
    encodeLog_bitCodec _ _ (outLen.eval n) 0 L, canonWord_eq din' (fun j => (dout' j).eval n),
    iCallNext_eq]

/-- The finalization's move word on the layout `iX O` is the canonical word of its next move. -/
theorem iFinMove_iX (O : QueryLog OUTER) (ph Lin : List Bool) (s : Fin (stateLen.eval n) → Bool)
    (bw : List Bool) {d : ℕ} (a : Fin d → Bool) (L : QueryLog OUTER) (cw Ow : List Bool) :
    iFinMove din' outLen finRun (pairEncode (XOF O) (iSt ph Lin (List.ofFn s) bw (List.ofFn a)
        ((COUT).encodeLog L) cw Ow)) =
      encodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n) (outLen.eval n)
        (iFinNext din' dout' stateLen outLen finRun n z ω s a L) := by
  rw [iFinMove_iSt din' outLen finRun (iX_inParam O), iX_ctx,
    encodeLog_bitCodec _ _ (outLen.eval n) 0 L, canonWord_eq din' (fun j => (dout' j).eval n),
    iFinNext_eq]

/-- **The finalization is replayed.** From a state word of the finalization with outer log `L`
and remaining budget `c`, reached after `t` rounds on every extension of the replayed prefix `P`,
the machine's next-move function replays `buildComp` of the finalization's rounds.

**Proof sketch.** Induction on `c`. The finalization's move word is the canonical word of its
next move (`iFinMove_iX`). An output `W` stops the machine with the word `⟨[true], W⟩`
(`iAct_fin_ret`, `iInv_stop`). A query at budget `0` stops it with the default
(`iAct_fin_timeout`). A query within budget is, on the prefix itself, the machine's next move
(`iAct_fin_stop`); on an extension by an entry with answer `y`, the entry is replayed
(`iAct_fin_ask`, `iInv_consume`, `encodeLog_append_single`) and the induction hypothesis applies to
the continuation. -/
theorem fin_phase (hist : QueryLog INNER) (s : Fin (stateLen.eval n) → Bool) (b : ℕ)
    (a : Fin (dα.eval n) → Bool) (hhist : hist.length ≤ q.eval n) (hb : b ≤ q.eval n) :
    ∀ (c : ℕ) (L : QueryLog OUTER) (t : ℕ) (P : QueryLog OUTER), L.length + c = finCall.eval n →
      INV t P (fun O' => iSt [false] ((CIN).encodeLog hist) (List.ofFn s) (List.replicate b true)
        (List.ofFn a) ((COUT).encodeLog L) (List.replicate c true) ((COUT).encodeLog O')) →
      t + c + 1 ≤ (iRounds q perCall finCall).eval n →
      ReplaysFrom (buildComp (iFinNext din' dout' stateLen outLen finRun n z ω s a) (zeroBits _) c
          L)
        (fun O' => NEXT (P ++ O')) := by
  intro c
  induction c with
  | zero =>
    intro L t P hL hinv ht
    cases hm : iFinNext din' dout' stateLen outLen finRun n z ω s a L with
    | ret W =>
      have hact : ACT (pairEncode (XOF P) (iSt [false] ((CIN).encodeLog hist) (List.ofFn s)
          (List.replicate b true) (List.ofFn a) ((COUT).encodeLog L) (List.replicate 0 true)
          ((COUT).encodeLog []))) = pairEncode [true] (pairEncode [true] (List.ofFn W)) :=
        iAct_fin_ret _ _ _ _ _ _ _ _ _ _ _ _ (by rw [iFinMove_iX, hm, encodeBitMove_ret])
      rw [buildComp_zero_of_ret hm, replaysFrom_pure_iff, List.append_nil,
        iInv_stop hinv hact (by omega), decodeBitMove_ret]
    | query j x' =>
      have hact : ACT (pairEncode (XOF P) (iSt [false] ((CIN).encodeLog hist) (List.ofFn s)
          (List.replicate b true) (List.ofFn a) ((COUT).encodeLog L) (List.replicate 0 true)
          ((COUT).encodeLog []))) =
          pairEncode [true] (pairEncode [true] (List.ofFn (zeroBits (outLen.eval n)))) := by
        rw [List.replicate_zero, ofFn_zeroBits]
        exact iAct_fin_timeout _ _ _ _ _ _ _ _ _ _ _ _ (iX_inParam P)
          (by rw [iFinMove_iX, hm, encodeBitMove_query])
      rw [buildComp_zero_of_query hm, replaysFrom_pure_iff, List.append_nil,
        iInv_stop hinv hact (by omega), decodeBitMove_ret]
  | succ c ih =>
    intro L t P hL hinv ht
    cases hm : iFinNext din' dout' stateLen outLen finRun n z ω s a L with
    | ret W =>
      have hact : ACT (pairEncode (XOF P) (iSt [false] ((CIN).encodeLog hist) (List.ofFn s)
          (List.replicate b true) (List.ofFn a) ((COUT).encodeLog L) (List.replicate (c + 1) true)
          ((COUT).encodeLog []))) = pairEncode [true] (pairEncode [true] (List.ofFn W)) :=
        iAct_fin_ret _ _ _ _ _ _ _ _ _ _ _ _ (by rw [iFinMove_iX, hm, encodeBitMove_ret])
      rw [buildComp_succ_of_ret hm, replaysFrom_pure_iff, List.append_nil,
        iInv_stop hinv hact (by omega), decodeBitMove_ret]
    | query j x' =>
      rw [buildComp_succ_of_query hm, replaysFrom_query_iff]
      refine ⟨?_, fun y => ?_⟩
      · have hact : ACT (pairEncode (XOF P) (iSt [false] ((CIN).encodeLog hist) (List.ofFn s)
            (List.replicate b true) (List.ofFn a) ((COUT).encodeLog L) (List.replicate (c + 1) true)
            ((COUT).encodeLog []))) = pairEncode [true] (pairEncode [false]
              (pairEncode (List.replicate j true) (List.ofFn x'))) := by
          rw [List.replicate_succ, MachineCodec.encodeLog_nil]
          exact iAct_fin_stop _ _ _ _ _ _ _ _ _ _ _ _
            (by rw [iFinMove_iX, hm, encodeBitMove_query])
        rw [List.append_nil, iInv_stop hinv hact (by omega), decodeBitMove_query]
      · have hinv' : INV (t + 1) (P ++ [⟨j, x', y⟩]) (fun O' => iSt [false] ((CIN).encodeLog hist)
            (List.ofFn s) (List.replicate b true) (List.ofFn a)
            ((COUT).encodeLog (L ++ [⟨j, x', y⟩])) (List.replicate c true) ((COUT).encodeLog O')) :=
                by
          intro O'
          have hb0 := iSt_le_iBound (A := A) (q := q) (dα := dα) (din := din) (dout := dout)
              (din' := din') (dout' := dout') (stateLen := stateLen) (perCall := perCall)
              (outLen := outLen) (finCall := finCall) (r := r) (init := init) (z := z) (ω := ω)
            (P ++ [⟨j, x', y⟩]) O' [false] (List.ofFn a) ((COUT).encodeLog (L ++ [⟨j, x', y⟩]))
            (List.replicate c true) hist s b (by decide) hhist hb (output_le_iCurBound a)
            (outLog_le _ (by rw [List.length_append, List.length_singleton]; omega))
            (by rw [List.length_replicate]; omega)
          rw [List.append_assoc, List.singleton_append] at hb0 ⊢
          refine runsTo_succ (hinv (⟨j, x', y⟩ :: O')) ?_ hb0
          beta_reduce
          rw [List.replicate_succ, MachineCodec.encodeLog_cons, encodeLog_append_single]
          exact iAct_fin_ask _ _ _ _ _ _ _ _ _ _ _ _ (by rw [iFinMove_iX, hm, encodeBitMove_query])
        have h := ih _ (t + 1) _ (by rw [List.length_append, List.length_singleton]; omega) hinv'
          (by omega)
        simp only [List.append_assoc, List.singleton_append] at h
        exact h


/-- **A call is replayed.** From a state word of a call on the inner query `x` to oracle `i`,
with outer log `L` and remaining budget `c`, the machine's next-move function replays `buildComp`
of the call's rounds followed by the rest of the reduction, given that the rest of the reduction
is replayed from every state word of the adversary after the call (`K`).

**Proof sketch.** Induction on `c`. The handler's move word is the canonical word of the call's
next move (`iCallMove_iX`). An answer `W = y ‖ s'`, or the joint default at budget `0`, ends the
call (`iAct_call_ret`, `iAct_call_timeout`, `iCallEnd_iSt`): the entry `⟨i, x, y⟩` is appended to
the adversary's log (`ofFn_take_drop_add`, `encodeLog_append_single`) and `K` applies, after the
monad law `pure_bind`. A query within budget is replayed as in the finalization (`iAct_call_stop`,
`iAct_call_ask`, `iInv_consume`, `query_bind`). -/
theorem call_phase (hist : QueryLog INNER) (s : Fin (stateLen.eval n) → Bool) (b : ℕ) (i : Fin k)
    (x : Fin ((din i).eval n) → Bool) (hlen : hist.length + b + 1 = q.eval n)
    (K : ∀ (y : Fin ((dout i).eval n) → Bool) (s' : Fin (stateLen.eval n) → Bool) (t : ℕ)
      (P : QueryLog OUTER),
      INV t P (fun O' => iSt [] ((CIN).encodeLog (hist ++ [⟨i, x, y⟩])) (List.ofFn s')
        (List.replicate b true) [] [] [] ((COUT).encodeLog O')) →
      t + (2 + finCall.eval n + b * (perCall.eval n + 2)) ≤ (iRounds q perCall finCall).eval n →
      ReplaysFrom (TREE (hist ++ [⟨i, x, y⟩]) s' b) (fun O' => NEXT (P ++ O'))) :
    ∀ (c : ℕ) (L : QueryLog OUTER) (t : ℕ) (P : QueryLog OUTER), L.length + c = perCall.eval n →
      INV t P (fun O' => iSt [true] ((CIN).encodeLog hist) (List.ofFn s) (List.replicate b true)
        (pairEncode (List.replicate i true) (List.ofFn x)) ((COUT).encodeLog L)
        (List.replicate c true) ((COUT).encodeLog O')) →
      t + c + 1 + (2 + finCall.eval n + b * (perCall.eval n + 2)) ≤
        (iRounds q perCall finCall).eval n →
      ReplaysFrom ((buildComp (iCallNext din dout din' dout' stateLen run n z ω s i x) (zeroBits _)
          c
          L).bind fun w => TREE (hist ++ [⟨i, x, fun j => w (Fin.castAdd (stateLen.eval n) j)⟩])
            (fun j => w (Fin.natAdd ((dout i).eval n) j)) b)
        (fun O' => NEXT (P ++ O')) := by
  -- The end of a call with the result `w`, at any budget word `cw`.
  have hend : ∀ (t : ℕ) (P : QueryLog OUTER) (L : QueryLog OUTER) (cw : List Bool)
      (w : Fin ((dout i).eval n + stateLen.eval n) → Bool),
      INV t P (fun O' => iSt [true] ((CIN).encodeLog hist) (List.ofFn s) (List.replicate b true)
        (pairEncode (List.replicate i true) (List.ofFn x)) ((COUT).encodeLog L) cw
        ((COUT).encodeLog O')) →
      (∀ O', ACT (pairEncode (XOF (P ++ O')) (iSt [true] ((CIN).encodeLog hist) (List.ofFn s)
        (List.replicate b true) (pairEncode (List.replicate i true) (List.ofFn x))
        ((COUT).encodeLog L) cw ((COUT).encodeLog O'))) =
        pairEncode [false] (iCallEnd dout (pairEncode (XOF (P ++ O')) (iSt [true]
          ((CIN).encodeLog hist) (List.ofFn s) (List.replicate b true)
          (pairEncode (List.replicate i true) (List.ofFn x)) ((COUT).encodeLog L) cw
          ((COUT).encodeLog O'))) (List.ofFn w))) →
      t + 1 + (2 + finCall.eval n + b * (perCall.eval n + 2)) ≤ (iRounds q perCall finCall).eval n →
      ReplaysFrom (TREE (hist ++ [⟨i, x, fun j => w (Fin.castAdd (stateLen.eval n) j)⟩])
        (fun j => w (Fin.natAdd ((dout i).eval n) j)) b) (fun O' => NEXT (P ++ O')) := by
    intro t P L cw w hinv hact ht
    refine K _ _ (t + 1) P (fun O' => ?_) ht
    refine runsTo_succ (hinv O') ?_ ?_
    · beta_reduce
      rw [hact, iCallEnd_iSt dout (iX_inParam _), List.length_replicate, selLen_eq,
        (ofFn_take_drop_add w).1, (ofFn_take_drop_add w).2, encodeLog_append_single,
        bitCodec_encodeEntry]
    · exact iSt_le_iBound (A := A) (q := q) (dα := dα) (din := din) (dout := dout) (din' := din')
        (dout' := dout') (stateLen := stateLen) (perCall := perCall) (outLen := outLen)
        (finCall := finCall) (r := r) (init := init) (z := z) (ω := ω)
        P O' [] [] [] [] _ _ b (by decide)
            (by rw [List.length_append, List.length_singleton]; omega) (by omega) (Nat.zero_le _)
        (Nat.zero_le _) (Nat.zero_le _)
  intro c
  induction c with
  | zero =>
    intro L t P hL hinv ht
    cases hm : iCallNext din dout din' dout' stateLen run n z ω s i x L with
    | ret W =>
      rw [buildComp_zero_of_ret hm, OracleComp.pure_bind]
      refine hend t P L _ W hinv (fun O' => ?_) (by omega)
      exact iAct_call_ret _ _ _ _ _ _ _ _ _ _ _ _ (by rw [iCallMove_iX, hm, encodeBitMove_ret])
    | query j x' =>
      rw [buildComp_zero_of_query hm, OracleComp.pure_bind]
      refine hend t P L _ (zeroBits _) hinv (fun O' => ?_) (by omega)
      have hact : ACT (pairEncode (XOF (P ++ O')) (iSt [true] ((CIN).encodeLog hist) (List.ofFn s)
          (List.replicate b true) (pairEncode (List.replicate i true) (List.ofFn x))
          ((COUT).encodeLog L) [] ((COUT).encodeLog O'))) =
          pairEncode [false] (iCallEnd dout (pairEncode (XOF (P ++ O')) (iSt [true]
            ((CIN).encodeLog hist) (List.ofFn s) (List.replicate b true)
            (pairEncode (List.replicate i true) (List.ofFn x)) ((COUT).encodeLog L) []
            ((COUT).encodeLog O')))
            (List.replicate (selLen dout n (List.replicate (↑i) true).length + stateLen.eval n)
              false)) :=
        iAct_call_timeout _ _ _ _ _ _ _ _ _ _ _ _ (iX_inParam _)
          (by rw [iCallMove_iX, hm, encodeBitMove_query])
      rw [List.length_replicate, selLen_eq, ← ofFn_zeroBits] at hact
      rw [List.replicate_zero]
      exact hact
  | succ c ih =>
    intro L t P hL hinv ht
    cases hm : iCallNext din dout din' dout' stateLen run n z ω s i x L with
    | ret W =>
      rw [buildComp_succ_of_ret hm, OracleComp.pure_bind]
      refine hend t P L _ W hinv (fun O' => ?_) (by omega)
      exact iAct_call_ret _ _ _ _ _ _ _ _ _ _ _ _ (by rw [iCallMove_iX, hm, encodeBitMove_ret])
    | query j x' =>
      rw [buildComp_succ_of_query hm, OracleComp.query_bind, replaysFrom_query_iff]
      refine ⟨?_, fun y => ?_⟩
      · have hact : ACT (pairEncode (XOF P) (iSt [true] ((CIN).encodeLog hist) (List.ofFn s)
            (List.replicate b true) (pairEncode (List.replicate i true) (List.ofFn x))
            ((COUT).encodeLog L) (List.replicate (c + 1) true) ((COUT).encodeLog []))) =
            pairEncode [true] (pairEncode [false]
              (pairEncode (List.replicate j true) (List.ofFn x'))) := by
          rw [List.replicate_succ, MachineCodec.encodeLog_nil]
          exact iAct_call_stop _ _ _ _ _ _ _ _ _ _ _ _
            (by rw [iCallMove_iX, hm, encodeBitMove_query])
        rw [List.append_nil, iInv_stop hinv hact (by omega), decodeBitMove_query]
      · have hinv' : INV (t + 1) (P ++ [⟨j, x', y⟩]) (fun O' => iSt [true] ((CIN).encodeLog hist)
            (List.ofFn s) (List.replicate b true) (pairEncode (List.replicate i true) (List.ofFn x))
            ((COUT).encodeLog (L ++ [⟨j, x', y⟩])) (List.replicate c true) ((COUT).encodeLog O')) :=
                by
          intro O'
          have hb0 := iSt_le_iBound (A := A) (q := q) (dα := dα) (din := din) (dout := dout)
              (din' := din') (dout' := dout') (stateLen := stateLen) (perCall := perCall)
              (outLen := outLen) (finCall := finCall) (r := r) (init := init) (z := z) (ω := ω)
            (P ++ [⟨j, x', y⟩]) O' [true] (pairEncode (List.replicate i true) (List.ofFn x))
            ((COUT).encodeLog (L ++ [⟨j, x', y⟩])) (List.replicate c true) hist s b (by decide)
            (by omega) (by omega) (query_le_iCurBound i x)
            (outLog_le _ (by rw [List.length_append, List.length_singleton]; omega))
            (by rw [List.length_replicate]; omega)
          rw [List.append_assoc, List.singleton_append] at hb0 ⊢
          refine runsTo_succ (hinv (⟨j, x', y⟩ :: O')) ?_ hb0
          beta_reduce
          rw [List.replicate_succ, MachineCodec.encodeLog_cons, encodeLog_append_single]
          exact iAct_call_ask _ _ _ _ _ _ _ _ _ _ _ _
              (by rw [iCallMove_iX, hm, encodeBitMove_query])
        have h := ih _ (t + 1) _ (by rw [List.length_append, List.length_singleton]; omega) hinv'
          (by omega)
        simp only [List.append_assoc, List.singleton_append] at h
        exact h

/-- **The rest of the reduction is replayed.** From a state word of the adversary with log
`hist` and remaining budget `b` (with `|hist| + b = q(n)`), reached after `t` rounds on every
extension of the replayed prefix `P`, the machine's next-move function replays `iTree`.

**Proof sketch.** Induction on `b`. The adversary's move word is the canonical word of its next
move (`iAdvMove_iX`). An output `a`, or a query at budget `0` (output `0^{dα(n)}`), opens the
finalization (`iAct_adv_ret`, `iAct_adv_timeout`), and `fin_phase` applies after
`buildComp_*_of_ret`/`_of_query`, `simulate_pure` and `pure_bind`. A query `x` to oracle `i`
within budget opens a call (`iAct_adv_query`); the simulation unfolds into the call followed by
the rest of the reduction (`simulate_query`, `iImpl_apply`, `bind_assoc`, `pure_bind`), and
`call_phase` applies with the induction hypothesis as its continuation. The round count decreases
along the way: `2 + finCall + b (perCall + 2)` rounds suffice. -/
theorem adv_phase : ∀ (b : ℕ) (hist : QueryLog INNER) (s : Fin (stateLen.eval n) → Bool) (t : ℕ)
    (P : QueryLog OUTER), hist.length + b = q.eval n →
    INV t P (fun O' => iSt [] ((CIN).encodeLog hist) (List.ofFn s) (List.replicate b true) [] [] []
      ((COUT).encodeLog O')) →
    t + (2 + finCall.eval n + b * (perCall.eval n + 2)) ≤ (iRounds q perCall finCall).eval n →
    ReplaysFrom (TREE hist s b) (fun O' => NEXT (P ++ O')) := by
  -- Opening the finalization with the adversary's output `a`.
  have hfin : ∀ (b : ℕ) (hist : QueryLog INNER) (s : Fin (stateLen.eval n) → Bool) (t : ℕ)
      (P : QueryLog OUTER) (a : Fin (dα.eval n) → Bool), hist.length + b = q.eval n →
      INV t P (fun O' => iSt [] ((CIN).encodeLog hist) (List.ofFn s) (List.replicate b true) [] []
          []
        ((COUT).encodeLog O')) →
      (∀ O', ACT (pairEncode (XOF (P ++ O')) (iSt [] ((CIN).encodeLog hist) (List.ofFn s)
        (List.replicate b true) [] [] [] ((COUT).encodeLog O'))) =
        pairEncode [false] (iSt [false] ((CIN).encodeLog hist) (List.ofFn s) (List.replicate b true)
          (List.ofFn a) ((COUT).encodeLog []) (List.replicate (finCall.eval n) true)
          ((COUT).encodeLog O'))) →
      t + 1 + (finCall.eval n) + 1 ≤ (iRounds q perCall finCall).eval n →
      ReplaysFrom (iFinish din' dout' stateLen outLen finCall finRun n z ω s a)
        (fun O' => NEXT (P ++ O')) := by
    intro b hist s t P a hlen hinv hact ht
    rw [iFinish_eq_buildComp]
    refine fin_phase hist s b a (by omega) (by omega) (finCall.eval n) [] (t + 1) P
      (by rw [List.length_nil, Nat.zero_add]) (fun O' => ?_) ht
    exact runsTo_succ (hinv O') (hact O') (iSt_le_iBound (A := A) (q := q) (dα := dα) (din := din)
        (dout := dout) (din' := din') (dout' := dout') (stateLen := stateLen) (perCall := perCall)
        (outLen := outLen) (finCall := finCall) (r := r) (init := init) (z := z) (ω := ω)
      P O' [false] (List.ofFn a) ((COUT).encodeLog [])
      (List.replicate (finCall.eval n) true) hist s b (by decide) (by omega) (by omega)
      (output_le_iCurBound a) (by rw [MachineCodec.encodeLog_nil]; exact Nat.zero_le _)
      (by rw [List.length_replicate]; omega))
  intro b
  induction b with
  | zero =>
    intro hist s t P hlen hinv ht
    cases hm : advNext A CIN n (advIn CTX) r hist with
    | ret a =>
      rw [iTree_eq, buildComp_zero_of_ret hm, simulate_pure, OracleComp.pure_bind]
      refine hfin 0 hist s t P a hlen hinv (fun O' => ?_) (by omega)
      rw [MachineCodec.encodeLog_nil]
      exact iAct_adv_ret _ _ _ _ _ _ _ _ _ _ _ _ (iX_inParam _)
        (by rw [iAdvMove_iX, hm, encodeBitMove_ret])
    | query i x =>
      rw [iTree_eq, buildComp_zero_of_query hm, simulate_pure, OracleComp.pure_bind]
      refine hfin 0 hist s t P _ hlen hinv (fun O' => ?_) (by omega)
      rw [MachineCodec.encodeLog_nil, List.replicate_zero, ofFn_zeroBits]
      exact iAct_adv_timeout _ _ _ _ _ _ _ _ _ _ _ _ (iX_inParam _)
        (by rw [iAdvMove_iX, hm, encodeBitMove_query])
  | succ b ih =>
    intro hist s t P hlen hinv ht
    cases hm : advNext A CIN n (advIn CTX) r hist with
    | ret a =>
      rw [iTree_eq, buildComp_succ_of_ret hm, simulate_pure, OracleComp.pure_bind]
      refine hfin (b + 1) hist s t P a hlen hinv (fun O' => ?_) (by rw [Nat.add_mul] at ht; omega)
      rw [MachineCodec.encodeLog_nil]
      exact iAct_adv_ret _ _ _ _ _ _ _ _ _ _ _ _ (iX_inParam _)
        (by rw [iAdvMove_iX, hm, encodeBitMove_ret])
    | query i x =>
      rw [iTree_eq, buildComp_succ_of_query hm, simulate_query, iImpl_apply]
      simp only [OracleComp.bind_assoc, OracleComp.pure_bind]
      rw [iCall_eq_buildComp]
      refine call_phase hist s b i x (by omega)
        (fun y s' t' P' hinv' ht' => ih _ s' t' P'
          (by rw [List.length_append, List.length_singleton]; omega) hinv' ht')
        (perCall.eval n) [] (t + 1) P (by rw [List.length_nil, Nat.zero_add])
        (fun O' => ?_) (by rw [Nat.add_mul] at ht; omega)
      refine runsTo_succ (hinv O') ?_ (iSt_le_iBound (A := A) (q := q) (dα := dα) (din := din)
          (dout := dout) (din' := din') (dout' := dout') (stateLen := stateLen) (perCall := perCall)
          (outLen := outLen) (finCall := finCall) (r := r) (init := init) (z := z) (ω := ω)
        P O' [true] (pairEncode (List.replicate i true) (List.ofFn x))
        ((COUT).encodeLog []) (List.replicate (perCall.eval n) true) hist s b (by decide) (by omega)
        (by omega) (query_le_iCurBound i x)
            (by rw [MachineCodec.encodeLog_nil]; exact Nat.zero_le _)
        (by rw [List.length_replicate]; omega))
      beta_reduce
      rw [MachineCodec.encodeLog_nil, List.replicate_succ]
      exact iAct_adv_query _ _ _ _ _ _ _ _ _ _ _ _ (iX_inParam _)
        (by rw [iAdvMove_iX, hm, encodeBitMove_query])

end Phases

/-- **The functional equation of the replay machine.** At parameter `n`, with the reduction's
input `z`, seed `ω`, the adversary's coins `r` and the initial state `s₀`, the computation of the
next-move function `O ↦ decodeBitMove (iRaw (iX O))` with budget `q(n) · perCall(n) + finCall(n)`
is the simulation of `A` on `advIn ⟨1^n, ⟨z, ω⟩⟩` by the handler, followed by the finalization.

**Proof sketch.** The reduction tree is `iTree [] s₀ q(n)` (`toCompOn_eq_advNext`). It makes at
most `q(n) · perCall(n) + finCall(n)` queries: `A` makes at most `q(n)` (`toCompOn_costBoundedBy`),
each answered by at most `perCall(n)` outer queries (`buildComp_costBoundedBy`,
`costBoundedBy_mul`, `simulate_costBoundedBy`), and the finalization makes at most `finCall(n)`
(`CostBoundedBy.bind`). The machine's next-move function replays it from the empty log
(`adv_phase` from the initial state, `runsTo_zero`), so `buildComp_of_replaysFrom` gives the
equality of trees. -/
theorem iRaw_spec (n : ℕ) (z ω : List Bool) (r : A.Coins n) (init : Fin (stateLen.eval n) → Bool) :
    buildComp (fun O => decodeBitMove (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
        (outLen.eval n) (iRaw A q dα din dout din' stateLen perCall outLen finCall run advIn finRun
            dout'
          (iX A din' dout' stateLen outLen n z ω r init O)))
      (zeroBits _) (q.eval n * perCall.eval n + finCall.eval n) [] =
      (simulate (iImpl din dout din' dout' stateLen perCall run n z ω)
          (A.toCompOn (bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n))
            n (q.eval n) (advIn (pairEncode (List.replicate n true) (pairEncode z ω))) r) init).bind
        fun res => iFinish din' dout' stateLen outLen finCall finRun n z ω res.2 res.1 := by
  have hT : (simulate (iImpl din dout din' dout' stateLen perCall run n z ω)
      (A.toCompOn (bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n))
        n (q.eval n) (advIn (pairEncode (List.replicate n true) (pairEncode z ω))) r) init).bind
      (fun res => iFinish din' dout' stateLen outLen finCall finRun n z ω res.2 res.1) =
      iTree A dα din dout din' dout' stateLen perCall outLen finCall run advIn finRun n z ω r []
        init (q.eval n) := by
    rw [toCompOn_eq_advNext, bitCodec_timeout, iTree_eq]
  rw [hT]
  -- The reduction makes at most `q · perCall + finCall` queries.
  have hcost : (iTree A dα din dout din' dout' stateLen perCall outLen finCall run advIn finRun n z
      ω r
      [] init (q.eval n)).CostBoundedBy (fun _ => 1) (q.eval n * perCall.eval n + finCall.eval n) :=
          by
    rw [← hT]
    have himpl : ∀ i x s, OracleComp.CostBoundedBy (fun _ => 1)
        (iImpl din dout din' dout' stateLen perCall run n z ω i x s) ((fun _ => perCall.eval n) i)
            := by
      intro i x s
      have h := (buildComp_costBoundedBy (iCallNext din dout din' dout' stateLen run n z ω s i x)
        (zeroBits _) (perCall.eval n) []).bind
        (f := fun w => OracleComp.pure (spec := bitSpec (fun j => (din' j).eval n)
          (fun j => (dout' j).eval n))
          ((fun j => w (Fin.castAdd (stateLen.eval n) j), fun j => w (Fin.natAdd ((dout i).eval n)
              j)) :
            (Fin ((dout i).eval n) → Bool) × (Fin (stateLen.eval n) → Bool)))
        (q₂ := 0) (fun _ => OracleComp.costBoundedBy_pure _ _ _)
      rw [Nat.add_zero] at h
      rw [iImpl_apply, iCall_eq_buildComp]
      exact h
    have hA := costBoundedBy_mul (NUPPT.toCompOn_costBoundedBy A
      (bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n)) n (q.eval n)
      (advIn (pairEncode (List.replicate n true) (pairEncode z ω))) r) (perCall.eval n)
    exact (simulate_costBoundedBy himpl hA init).bind fun res => by
      rw [iFinish_eq_buildComp]
      exact buildComp_costBoundedBy _ _ _ _
  -- The machine replays the reduction from the empty log.
  have hinv : IInv A q dα din dout din' dout' stateLen perCall outLen finCall run advIn finRun
      n z ω r init 0 [] (fun O' => iSt []
        ((bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n)).encodeLog [])
        (List.ofFn init) (List.replicate (q.eval n) true) [] [] []
        ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
          (outLen.eval n)).encodeLog O')) := by
    intro O'
    have hs : iStart q (iX A din' dout' stateLen outLen n z ω r init ([] ++ O')) = iSt []
        ((bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) (dα.eval n)).encodeLog [])
        (List.ofFn init) (List.replicate (q.eval n) true) [] [] []
        ((bitCodec (fun j => (din' j).eval n) (fun j => (dout' j).eval n)
          (outLen.eval n)).encodeLog O') := by
      rw [iStart_eq, iX_inAdvice, pairSndD_pairEncode, iX_inParam, List.length_replicate, iX_outer,
        List.nil_append, MachineCodec.encodeLog_nil]
    beta_reduce
    rw [← hs]
    exact runsTo_zero (by
      rw [hs]
      exact iSt_le_iBound (A := A) (q := q) (dα := dα) (din := din) (dout := dout) (din' := din')
          (dout' := dout') (stateLen := stateLen) (perCall := perCall) (outLen := outLen)
          (finCall := finCall) (r := r) (init := init) (z := z) (ω := ω)
        [] O' [] [] [] [] [] init (q.eval n) (by decide) (Nat.zero_le _) le_rfl
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _))
  have hrep := adv_phase (A := A) (q := q) (dα := dα) (din := din) (dout := dout) (din' := din')
    (dout' := dout') (stateLen := stateLen) (perCall := perCall) (outLen := outLen)
    (finCall := finCall) (run := run) (advIn := advIn) (finRun := finRun) (init := init)
    (q.eval n) [] init 0 [] (by rw [List.length_nil, Nat.zero_add]) hinv (by
      rw [iRounds_eq]
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
      omega)
  exact buildComp_of_replaysFrom _ _ _ [] _ hrep hcost
end Spec

end TCSlib.Cryptography.Games.EffFill

## ===== TCSlib/Cryptography/Games/Efficiency/OracleBridge.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Efficiency.Strings
import TCSlib.Cryptography.Games.Bridges.QueryTree
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# From one-oracle `bitCodec` machines to next-query machines (efficiency fill, T4)

The translators behind `Games.exists_toOracleAdversary_of_bitCodec` (route note
`briefs/pass-shelat-ch5-8/design/S2b-efficiency.md`, §"T4"). A machine `B` against one
`bitCodec` oracle with a one-bit output reads `⟨[], log⟩` and writes `bitCodec` moves; a
next-query machine of the ch. 2–4 layer reads a history (`encodeHist`) and writes
`decodeOracleMove` moves. Two polynomial-time maps translate:
- `bridgePre` turns the history `⟨⟨x₁, y₁⟩, ⟨…, []⟩⟩` into `⟨[], ⟨⟨[], ⟨x₁, y₁⟩⟩, ⟨…, []⟩⟩⟩`,
  the empty input followed by the `bitCodec` log (the index of the only oracle is `1^0 = []`);
- `bridgePost` turns a canonical query word `⟨[false], ⟨[], x⟩⟩` into `⟨[false], x⟩`, the word
  `⟨[true], [true]⟩` into the verdict `[true, true]`, and every other word into `[true, false]`.

Both decoders check the payload length `ℓ₁(n)` themselves and agree on it, so neither map
needs the parameter.

## Main definitions

* `EffFill.relabelEmit`, `EffFill.relabel`, `EffFill.bridgePre`, `EffFill.bridgePost`.

## Main results

* `EffFill.bridgePre_encodeHist`: the history of a log translates to the log.
* `EffFill.bridgePost_spec`: the translated move is the decoded move.
* `EffFill.eval_buildTree_bridge`: the two computations evaluate alike against every oracle.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definition 96.1 (oracle indistinguishability against oracle machines).
-/

namespace TCSlib.Cryptography.Games.EffFill

open Complexity Turing

/-! ### The history translator -/

/-- The piece emitted for the suffix `w` of an encoded history: `⟨⟨[], fst w⟩, []⟩` for a
non-empty suffix, nothing for the empty one. -/
def relabelEmit (w : List Bool) : List Bool :=
  if w = [] then [] else pairEncode (pairEncode [] (pairFstD w)) []

/-- `relabelEmit w = if w = [] then [] else ⟨⟨[], fst w⟩, []⟩`. -/
theorem relabelEmit_eq (w : List Bool) :
    relabelEmit w = if w = [] then [] else pairEncode (pairEncode [] (pairFstD w)) [] :=
  rfl

/-- The pieces of the first `m` suffixes `w, snd w, snd (snd w), …`, concatenated. -/
def relabelN (m : ℕ) (w : List Bool) : List Bool :=
  (List.range m).flatMap fun i => relabelEmit (pairSndD^[i] w)

/-- `relabelN m w = ⋃_{i < m} relabelEmit (snd^i w)`. -/
theorem relabelN_eq (m : ℕ) (w : List Bool) :
    relabelN m w = (List.range m).flatMap fun i => relabelEmit (pairSndD^[i] w) :=
  rfl

/-- **The history translator's body:** the pieces of the first `|x| + 1` suffixes of `x`. -/
def relabel (x : List Bool) : List Bool := relabelN (x.length + 1) x

/-- `relabel x = relabelN (|x| + 1) x`. -/
theorem relabel_eq (x : List Bool) : relabel x = relabelN (x.length + 1) x := rfl

/-- **The history translator:** `bridgePre x = ⟨[], relabel x⟩`. -/
def bridgePre (x : List Bool) : List Bool := pairEncode [] (relabel x)

/-- `bridgePre x = ⟨[], relabel x⟩`. -/
theorem bridgePre_eq (x : List Bool) : bridgePre x = pairEncode [] (relabel x) := rfl

/-- The empty word has no pieces: `relabelN m [] = []`. -/
theorem relabelN_nil (m : ℕ) : relabelN m [] = [] := by
  rw [relabelN_eq, List.flatMap_eq_nil_iff]
  intro i _
  have h : ∀ j, pairSndD^[j] ([] : List Bool) = [] := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih]
      exact pairSndD_of_pairDecode_eq_none Turing.pairDecode_nil
  rw [h, relabelEmit_eq, if_pos rfl]

/-- One more suffix: `relabelN (m + 1) w = relabelEmit w ++ relabelN m (snd w)`. -/
theorem relabelN_succ (m : ℕ) (w : List Bool) :
    relabelN (m + 1) w = relabelEmit w ++ relabelN m (pairSndD w) := by
  rw [relabelN_eq, relabelN_eq, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  rfl

/-- The history of a one-oracle `bitCodec` log, as (query, answer) pairs. -/
def logHist {ℓ₁ ℓ₂ : ℕ} (L : QueryLog (bitSpec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂))) :
    List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) :=
  L.map fun e => (e.2.1, e.2.2)

/-- `logHist L` maps each entry `⟨0, x, y⟩` to `(x, y)`. -/
theorem logHist_eq {ℓ₁ ℓ₂ : ℕ} (L : QueryLog (bitSpec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂))) :
    logHist L = L.map fun e => (e.2.1, e.2.2) :=
  rfl

/-- **The pieces of an encoded history form the `bitCodec` log:** for every `m ≥ |L|`,
`relabelN m (encodeHist (logHist L)) = encodeLog L`.

**Proof sketch.** Induction on `L`. The empty history is `[]`, which has no pieces
(`relabelN_nil`). A non-empty history `⟨⟨x, y⟩, rest⟩` emits `⟨⟨[], ⟨x, y⟩⟩, []⟩` and continues
with `rest` (`relabelN_succ`, `encodeHist_cons`); the piece is the entry's `bitCodec` encoding
(`bitCodec_encodeEntry`, the index of the only oracle being `1^0 = []`), and the concatenation is
the nested pair (`GGMRed.pairEncode_append_right`, `encodeLog_cons`). -/
theorem relabelN_encodeHist {ℓ₁ ℓ₂ : ℕ} (dα : ℕ) :
    ∀ (L : QueryLog (bitSpec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂))) (m : ℕ), L.length ≤ m →
      relabelN m (encodeHist (logHist L)) =
        (bitCodec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) dα).encodeLog L
  | [], m, _ => by
    rw [logHist_eq, List.map_nil, encodeHist_nil, relabelN_nil, MachineCodec.encodeLog_nil]
  | e :: L, m, hm => by
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by rw [List.length_cons] at hm; omega⟩
    rw [logHist_eq, List.map_cons, ← logHist_eq, encodeHist_cons, relabelN_succ,
      pairSndD_pairEncode, relabelN_encodeHist dα L m (by rw [List.length_cons] at hm; omega),
      relabelEmit_eq, if_neg (pairEncode_ne_nil _ _), pairFstD_pairEncode,
      MachineCodec.encodeLog_cons, bitCodec_encodeEntry, ← GGMRed.pairEncode_append_right,
      List.nil_append, Fin.fin_one_eq_zero e.1, Fin.val_zero, List.replicate_zero]

/-- An encoded history has at least as many bits as entries. -/
theorem length_le_length_encodeHist {ℓ₁ ℓ₂ : ℕ} :
    ∀ h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)), h.length ≤ (encodeHist h).length
  | [] => Nat.zero_le _
  | p :: h => by
    rw [encodeHist_cons, length_pairEncode, List.length_cons]
    have := length_le_length_encodeHist h
    omega

/-- **The history translator on a history:** `bridgePre (encodeHist (logHist L)) =
⟨[], encodeLog L⟩`. -/
theorem bridgePre_encodeHist {ℓ₁ ℓ₂ : ℕ} (dα : ℕ)
    (L : QueryLog (bitSpec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂))) :
    bridgePre (encodeHist (logHist L)) =
      pairEncode [] ((bitCodec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) dα).encodeLog L) := by
  rw [bridgePre_eq, relabel_eq, relabelN_encodeHist dα L _]
  have h1 := length_le_length_encodeHist (logHist L)
  rw [logHist_eq, List.length_map] at h1
  rw [logHist_eq]
  omega

/-- The emitted piece is polynomial-time. -/
theorem relabelEmit_poly : PolyTimeComputable relabelEmit :=
  (polyTimeComputable_ite polyTimeComputable_isNil (polyTimeComputable_const [])
    (((polyTimeComputable_const []).pairEncode polyTimeComputable_pairFstD).pairEncode
      (polyTimeComputable_const []))).congr fun w => by
    rw [relabelEmit_eq]
    by_cases h : w = []
    · rw [if_pos h, decide_eq_true h]
      rfl
    · rw [if_neg h, decide_eq_false h]
      rfl

/-- **The history translator is polynomial-time** (`Complexity.polyTimeComputable_iterateEmit`
with the step `pairSndD`, `|x| + 1` rounds and the orbit bound `|x|`). -/
theorem bridgePre_poly : PolyTimeComputable bridgePre := by
  have horbit : ∀ (x : List Bool) (i : ℕ), i ≤ PolyExpr.var.eval x.length →
      (pairSndD^[i] x).length ≤ PolyExpr.var.eval x.length := by
    intro x i _
    clear * -
    rw [PolyExpr.eval_var]
    induction i with
    | zero => exact le_rfl
    | succ i ih => rw [Function.iterate_succ_apply']; exact (length_pairSndD_le _).trans ih
  have h := polyTimeComputable_iterateEmit polyTimeComputable_pairSndD relabelEmit_poly .var .var
    horbit
  refine ((polyTimeComputable_const []).pairEncode h).congr fun x => ?_
  rw [bridgePre_eq, relabel_eq, relabelN_eq, PolyExpr.eval_var]

/-! ### The move translator -/

/-- **The move translator:** a canonical query word `⟨[false], ⟨[], x⟩⟩` becomes `⟨[false], x⟩`,
the output word `⟨[true], [true]⟩` becomes `[true, true]`, and every other word `[true, false]`. -/
def bridgePost (w : List Bool) : List Bool :=
  if w = pairEncode [false] (pairEncode [] (pairSndD (pairSndD w))) then
    pairEncode [false] (pairSndD (pairSndD w))
  else if w = pairEncode [true] [true] then [true, true] else [true, false]

/-- The defining equation of `bridgePost`. -/
theorem bridgePost_eq (w : List Bool) :
    bridgePost w =
      if w = pairEncode [false] (pairEncode [] (pairSndD (pairSndD w))) then
        pairEncode [false] (pairSndD (pairSndD w))
      else if w = pairEncode [true] [true] then [true, true] else [true, false] :=
  rfl

/-- **The move translator is polynomial-time** (`eq_poly` for the two tests). -/
theorem bridgePost_poly : PolyTimeComputable bridgePost := by
  have hx := polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD
  have h1 := eq_poly polyTimeComputable_id ((polyTimeComputable_const [false]).pairEncode
    ((polyTimeComputable_const []).pairEncode hx))
  have h2 := eq_poly polyTimeComputable_id (polyTimeComputable_const (pairEncode [true] [true]))
  refine (polyTimeComputable_ite h1 ((polyTimeComputable_const [false]).pairEncode hx)
    (polyTimeComputable_ite h2 (polyTimeComputable_const [true, true])
      (polyTimeComputable_const [true, false]))).congr fun w => ?_
  rw [bridgePost_eq]
  simp only [id_eq, decide_eq_true_eq]

/-- **The translated move is the decoded move.** For every word `w`, either `decodeBitMove`
reads the query `x` (to the only oracle) and `decodeOracleMove` reads the query `x` off
`bridgePost w`, or `decodeBitMove` reads an output `a` and `decodeOracleMove` the verdict `a 0`.

**Proof sketch.** Three cases on `w`. A word `⟨[false], ⟨[], x⟩⟩` becomes `⟨[false], x⟩`: if
`|x| = ℓ₁` both decoders read the query (`decodeBitMove_query`,
`decodeOracleMove_pairEncode_ofFn`); otherwise both read the default, the all-`false` output and
the verdict `false` (`decodeBitMove_of_not_canonical`,
`decodeOracleMove_pairEncode_false_of_length_ne`). The word `⟨[true], [true]⟩` reads the output
`1` on both sides (`decodeBitMove_ret`, `decodeOracleMove_true_two`). Every other word becomes
`[true, false]`, the verdict `false`; `decodeBitMove` reads either the output `0` (the word
`⟨[true], [false]⟩`) or the default (`decodeBitMove_of_not_canonical`); its query words are all
of the first form, since `1^i = []` for `i : Fin 1`. -/
theorem bridgePost_spec (ℓ₁ ℓ₂ : ℕ) (w : List Bool) :
    (∃ x : Fin ℓ₁ → Bool,
      decodeBitMove (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1 w = .query 0 x ∧
        decodeOracleMove ℓ₁ (bridgePost w) = .query x) ∨
    (∃ a : Fin 1 → Bool,
      decodeBitMove (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1 w = .ret a ∧
        decodeOracleMove ℓ₁ (bridgePost w) = .ret (a 0)) := by
  by_cases hq : w = pairEncode [false] (pairEncode [] (pairSndD (pairSndD w)))
  · rw [bridgePost_eq, if_pos hq]
    set xw := pairSndD (pairSndD w)
    by_cases hx : xw.length = ℓ₁
    · obtain ⟨x, hxe⟩ := exists_ofFn_eq hx
      refine Or.inl ⟨x, ?_, ?_⟩
      · rw [hq, ← hxe]
        exact decodeBitMove_query (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1 0 x
      · rw [← hxe]
        exact decodeOracleMove_pairEncode_ofFn ℓ₁ x
    · refine Or.inr ⟨zeroBits 1, ?_, ?_⟩
      · refine decodeBitMove_of_not_canonical (fun i x h => hx ?_) (fun a h => ?_)
        · rw [hq, Fin.fin_one_eq_zero i, Fin.val_zero, List.replicate_zero] at h
          have h' := congrArg (fun v => pairSndD (pairSndD v)) h
          simp only [pairSndD_pairEncode] at h'
          rw [h', List.length_ofFn]
        · rw [hq] at h
          have h' := congrArg pairFstD h
          simp only [pairFstD_pairEncode] at h'
          exact absurd h' (by decide)
      · rw [decodeOracleMove_pairEncode_false_of_length_ne ℓ₁ hx, zeroBits_apply]
  · by_cases hr : w = pairEncode [true] [true]
    · refine Or.inr ⟨fun _ => true, ?_, ?_⟩
      · rw [hr]
        exact decodeBitMove_ret (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1 (fun _ => true)
      · rw [bridgePost_eq, if_neg hq, if_pos hr]
        exact decodeOracleMove_true_two ℓ₁ true
    · rw [bridgePost_eq, if_neg hq, if_neg hr, decodeOracleMove_true_two]
      by_cases hf : w = pairEncode [true] [false]
      · refine Or.inr ⟨fun _ => false, ?_, rfl⟩
        rw [hf]
        exact decodeBitMove_ret (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1 (fun _ => false)
      · refine Or.inr ⟨zeroBits 1, ?_, by rw [zeroBits_apply]⟩
        refine decodeBitMove_of_not_canonical (fun i x h => hq ?_) (fun a h => ?_)
        · rw [h, Fin.fin_one_eq_zero i, Fin.val_zero, List.replicate_zero, pairSndD_pairEncode,
            pairSndD_pairEncode]
        · have ha : List.ofFn a = [a 0] := by rw [List.ofFn_succ, List.ofFn_zero]
          rw [ha] at h
          cases h0 : a 0
          · rw [h0] at h; exact hf h
          · rw [h0] at h; exact hr h

/-! ### Evaluation -/

/-- **The two computations evaluate alike.** For a string function `D` (a machine with fixed coins),
the ch. 2–4 tree of the next-move function `h ↦ decodeOracleMove ℓ₁ (bridgePost (D (bridgePre
(encodeHist h))))` from the history of a log `L`, evaluated against `f`, is bit `0` of the
`bitCodec` computation of `L ↦ decodeBitMove (D ⟨[], encodeLog L⟩)` from `L`, evaluated against
`f` at the only oracle; for every budget.

**Proof sketch.** Induction on the budget, generalizing the log. The history translates to the
log (`bridgePre_encodeHist`), so both next moves come from the same word, and `bridgePost_spec`
gives corresponding moves. An output `a` gives the leaf `a 0` against the leaf `a`
(`buildTree_*_of_ret`, `buildComp_*_of_ret`). A query with the budget spent gives the verdict
`false` against `zeroBits 1`, whose bit `0` is `false`. A query `x` within budget asks `f x` on
both sides (`QueryTree.eval_query`, `OracleComp.evalFn_query`), and the continuations agree by
induction, since the history of `L ++ [⟨0, x, f x⟩]` is that of `L` followed by `(x, f x)`. -/
theorem eval_buildTree_bridge (ℓ₁ ℓ₂ : ℕ) (D : List Bool → List Bool)
    (f : (Fin ℓ₁ → Bool) → (Fin ℓ₂ → Bool)) :
    ∀ (q : ℕ) (L : QueryLog (bitSpec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂))),
      (buildTree (fun h => decodeOracleMove ℓ₁ (bridgePost (D (bridgePre (encodeHist h))))) q
          (logHist L)).eval f =
        (buildComp (fun L => decodeBitMove (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1
            (D (pairEncode [] ((bitCodec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1).encodeLog L))))
          (zeroBits 1) q L).evalFn (fun _ => f) 0 := by
  intro q
  induction q with
  | zero =>
    intro L
    rcases bridgePost_spec ℓ₁ ℓ₂ (D (pairEncode []
        ((bitCodec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1).encodeLog L))) with
      ⟨x, hb, ho⟩ | ⟨a, hb, ho⟩
    · rw [buildTree_zero_of_query (x := x) (by rw [bridgePre_encodeHist 1 L]; exact ho),
        buildComp_zero_of_query hb, QueryTree.eval_ret, OracleComp.evalFn_pure, zeroBits_apply]
    · rw [buildTree_zero_of_ret (b := a 0) (by rw [bridgePre_encodeHist 1 L]; exact ho),
        buildComp_zero_of_ret hb, QueryTree.eval_ret, OracleComp.evalFn_pure]
  | succ q ih =>
    intro L
    rcases bridgePost_spec ℓ₁ ℓ₂ (D (pairEncode []
        ((bitCodec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1).encodeLog L))) with
      ⟨x, hb, ho⟩ | ⟨a, hb, ho⟩
    · rw [buildTree_succ_of_query (x := x) (by rw [bridgePre_encodeHist 1 L]; exact ho),
        buildComp_succ_of_query hb, QueryTree.eval_query, OracleComp.evalFn_query]
      have hh : logHist L ++ [(x, f x)] = logHist (L ++ [⟨0, x, f x⟩]) := by
        rw [logHist_eq, logHist_eq, List.map_append, List.map_singleton]
      rw [hh]
      exact ih (L ++ [⟨0, x, f x⟩])
    · rw [buildTree_succ_of_ret (b := a 0) (by rw [bridgePre_encodeHist 1 L]; exact ho),
        buildComp_succ_of_ret hb, QueryTree.eval_ret, OracleComp.evalFn_pure]

end TCSlib.Cryptography.Games.EffFill

## ===== TCSlib/Cryptography/Games/Efficiency/Replay.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Machines

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Replaying a computation with a next-move function (efficiency fill, S3)

A next-move function `f` (of the log so far) **replays** an oracle computation `t` when `f []` is
`t`'s first move and, at a query, `f` extended by the query and any answer replays the
continuation (`ReplaysFrom`). If it does and `t` makes at most `b` queries, then `buildComp` of `f`
with budget `b` is `t` itself (`buildComp_of_replaysFrom`): the budget never cuts the replay
short. The interactive efficiency target (`Games.exists_interactiveHandlerMachine`) uses it, with
the cost scaling lemma `costBoundedBy_mul` (route note
`briefs/pass-shelat-ch5-8/design/S2b-efficiency.md`, §"Shared pieces", S3, and §"T2", step 4).

## Main definitions

* `EffFill.ReplaysFrom t f`: the next-move function `f` replays `t`.

## Main results

* `EffFill.buildComp_of_replaysFrom`: a replay within budget builds the computation.
* `EffFill.costBoundedBy_mul`: charging `p` per query multiplies a query bound by `p`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §3.8.1 (oracle machines).
-/

namespace TCSlib.Cryptography.Games.EffFill

variable {ι α : Type} {spec : OracleSpec ι}

/-- **`f` replays `t`:** at a return `a`, `f []` is the output `a`; at a query `x` to oracle `i`
with continuation `k`, `f []` is that query and, for every answer `y`, the function
`O ↦ f (⟨i, x, y⟩ :: O)` replays `k y`. (The argument of `f` is the log after the current
position.) -/
def ReplaysFrom : OracleComp spec α → (QueryLog spec → Move spec α) → Prop
  | .pure a, f => f [] = .ret a
  | .query i x k, f => f [] = .query i x ∧ ∀ y, ReplaysFrom (k y) fun O => f (⟨i, x, y⟩ :: O)

/-- A return is replayed when the function outputs it: `ReplaysFrom (pure a) f ↔ f [] = ret a`. -/
theorem replaysFrom_pure_iff (a : α) (f : QueryLog spec → Move spec α) :
    ReplaysFrom (.pure a) f ↔ f [] = .ret a :=
  Iff.rfl

/-- A query is replayed when the function asks it and replays every continuation:
`ReplaysFrom (query i x k) f ↔ f [] = query i x ∧ ∀ y, ReplaysFrom (k y) (f ∘ (⟨i, x, y⟩ :: ·))`. -/
theorem replaysFrom_query_iff (i : ι) (x : spec.dom i) (k : spec.rng i → OracleComp spec α)
    (f : QueryLog spec → Move spec α) :
    ReplaysFrom (.query i x k) f ↔
      f [] = .query i x ∧ ∀ y, ReplaysFrom (k y) fun O => f (⟨i, x, y⟩ :: O) :=
  Iff.rfl

/-- **A replay within budget builds the computation.** If `O ↦ next (hist ++ O)` replays `t` and
`t` makes at most `b` queries, then `buildComp next timeout b hist = t`.

**Proof sketch.** Induction on `t`, generalizing the log and the budget. A return `a` is
`next hist = ret a`, and `buildComp` returns `a` at every budget (`buildComp_zero_of_ret`,
`buildComp_succ_of_ret`). A query costs `1 ≤ b`, so `b = b' + 1`, and `buildComp` asks the same
query (`buildComp_succ_of_query`); each continuation is replayed from `hist ++ [⟨i, x, y⟩]`
(`List.append_assoc`) within `b'`, and agrees by induction. -/
theorem buildComp_of_replaysFrom (next : QueryLog spec → Move spec α) (timeout : α) :
    ∀ (t : OracleComp spec α) (hist : QueryLog spec) (b : ℕ),
      ReplaysFrom t (fun O => next (hist ++ O)) → t.CostBoundedBy (fun _ => 1) b →
        buildComp next timeout b hist = t := by
  intro t
  induction t with
  | pure a =>
    intro hist b h _
    have h' : next hist = .ret a := by
      have := (replaysFrom_pure_iff a _).1 h
      rwa [List.append_nil] at this
    cases b with
    | zero => exact buildComp_zero_of_ret h'
    | succ b => exact buildComp_succ_of_ret h'
  | query i x k ih =>
    intro hist b h hc
    obtain ⟨h1, h2⟩ := (replaysFrom_query_iff i x k _).1 h
    rw [List.append_nil] at h1
    obtain ⟨hb, hk⟩ := (OracleComp.costBoundedBy_query _ i x k b).1 hc
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    rw [buildComp_succ_of_query h1]
    refine congrArg (OracleComp.query i x) (funext fun y => ih y _ b ?_ ?_)
    · have e : (fun O => next ((hist ++ [⟨i, x, y⟩]) ++ O)) =
          fun O => next (hist ++ ⟨i, x, y⟩ :: O) := by
        funext O
        rw [List.append_assoc, List.singleton_append]
      rw [e]
      exact h2 y
    · have := hk y
      rwa [Nat.add_sub_cancel] at this

/-- **Charging `p` per query multiplies the bound by `p`:** a computation with at most `q` queries
is cost-bounded by `q · p` when every query costs `p`.

**Proof sketch.** Induction on the computation: a query needs `1 ≤ q`, so `p ≤ q · p`, and the
continuation's bound `(q − 1) · p` is `q · p − p` (`Nat.sub_one_mul`). -/
theorem costBoundedBy_mul {c : OracleComp spec α} {q : ℕ}
    (h : c.CostBoundedBy (fun _ => 1) q) (p : ℕ) : c.CostBoundedBy (fun _ => p) (q * p) := by
  induction c generalizing q with
  | pure a => exact OracleComp.costBoundedBy_pure _ _ _
  | query i x k ih =>
    obtain ⟨hq, hk⟩ := (OracleComp.costBoundedBy_query _ i x k q).1 h
    refine (OracleComp.costBoundedBy_query _ i x k _).2 ⟨?_, fun y => ?_⟩
    · exact Nat.le_mul_of_pos_left p hq
    · rw [← Nat.sub_one_mul]
      exact ih y (hk y)

end TCSlib.Cryptography.Games.EffFill

## ===== TCSlib/Cryptography/Games/Efficiency/Strings.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Reduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The string layer of the efficiency fill

The machines of the efficiency targets (`TCSlib.Cryptography.Games.Efficiency`) replay a reduction
on strings. This file collects the string-level pieces they share (route note
`briefs/pass-shelat-ch5-8/design/S2b-efficiency.md`, §"Shared pieces", S1 and S2):
- appending one entry to an encoded log is a concatenation (`encodeLog_append_single`);
- fixed-length decoding with the all-`false` default, as a string function (`fixLen`);
- a `k`-way selection of a polynomial length by an index written in unary (`selLen`), and finite
  sums of polynomials (`sumPoly`);
- the **canonical decoder** `canonWord`: on every word it returns the canonical word of the move
  that `decodeBitMove` reads off it, and it is polynomial-time (`canonFun_poly`); canonicity is
  tested by re-encoding and comparing;
- an **activation loop** (`actLoop`): `GGMRed.stateLoopFun` with one activation per round, the
  activation returning `⟨[false], new state⟩` to continue or `⟨[true], output⟩` to stop, with its
  run invariant `RunsTo`;
- the machine glue (`exists_splitMachine`): a polynomial-time function of the raw layout becomes a
  machine whose first `p(n)` coins are a seed passed as data.

## Main definitions

* `EffFill.fixLen`, `EffFill.selLen`, `EffFill.sumPoly`, `EffFill.canonWord`, `EffFill.canonFun`.
* `EffFill.actLoop`, `EffFill.RunsTo`.

## Main results

* `EffFill.encodeLog_append_single`, `EffFill.ofFn_getD_decodeFin`.
* `EffFill.canonWord_eq`: the canonical decoder is `encodeBitMove ∘ decodeBitMove`.
* `EffFill.canonFun_poly`, `EffFill.fixLen_poly`, `EffFill.selLen_poly`, `EffFill.actLoop_poly`.
* `EffFill.runsTo_stop`: a run that stops evaluates the loop.
* `EffFill.exists_splitMachine`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §2.1 (closure of p.p.t. machines under efficient operations) and §3.8.1 (oracle machines).
-/

namespace TCSlib.Cryptography.Games.EffFill

open Complexity Turing

variable {k : ℕ}

/-! ### Logs -/

/-- **Appending one entry to a log appends one pair:** `codec.encodeLog (h ++ [e]) =
codec.encodeLog h ++ pairEncode (codec.encodeEntry e) []` (the nested encoding is flat). -/
theorem encodeLog_append_single {ι α : Type} {spec : OracleSpec ι} (codec : MachineCodec spec α)
    (h : QueryLog spec) (e : Σ i, spec.dom i × spec.rng i) :
    codec.encodeLog (h ++ [e]) = codec.encodeLog h ++ pairEncode (codec.encodeEntry e) [] := by
  induction h with
  | nil =>
    rw [List.nil_append, MachineCodec.encodeLog_cons, MachineCodec.encodeLog_nil, List.nil_append]
  | cons e' h ih =>
    rw [List.cons_append, MachineCodec.encodeLog_cons, MachineCodec.encodeLog_cons, ih,
      GGMRed.pairEncode_append_right]

/-- An encoded log is at most `E` bits per entry when each entry, as a pair `⟨e, rest⟩`, adds at
most `E` bits: `|codec.encodeLog h| ≤ |h| · E`. -/
theorem length_encodeLog_le {ι α : Type} {spec : OracleSpec ι} (codec : MachineCodec spec α)
    (E : ℕ) : ∀ (h : QueryLog spec), (∀ e ∈ h, 2 * (codec.encodeEntry e).length + 2 ≤ E) →
      (codec.encodeLog h).length ≤ h.length * E
  | [], _ => by rw [MachineCodec.encodeLog_nil]; exact Nat.zero_le _
  | e :: h, hE => by
    rw [MachineCodec.encodeLog_cons, length_pairEncode, List.length_cons, Nat.add_mul, Nat.one_mul]
    have h1 := hE e List.mem_cons_self
    have h2 := length_encodeLog_le codec E h fun e' he' => hE e' (List.mem_cons_of_mem e he')
    omega

/-- The encoding of a log ends with the encoding of each of its suffixes, so it is at least as
long: `|codec.encodeLog O| ≤ |codec.encodeLog (P ++ O)|`. -/
theorem length_encodeLog_le_append {ι α : Type} {spec : OracleSpec ι} (codec : MachineCodec spec α)
    (O : QueryLog spec) : ∀ P : QueryLog spec,
      (codec.encodeLog O).length ≤ (codec.encodeLog (P ++ O)).length
  | [] => by rw [List.nil_append]
  | e :: P => by
    rw [List.cons_append, MachineCodec.encodeLog_cons, length_pairEncode]
    have := length_encodeLog_le_append codec O P
    omega

/-! ### Fixed-length decoding with a default -/

/-- The word `w` if it has `d` bits, and the all-`false` word of `d` bits otherwise. -/
def fixLen (d : ℕ) (w : List Bool) : List Bool :=
  if w.length = d then w else List.replicate d false

/-- `fixLen d w = if |w| = d then w else 0^d`. -/
theorem fixLen_eq (d : ℕ) (w : List Bool) :
    fixLen d w = if w.length = d then w else List.replicate d false :=
  rfl

/-- A word of the right length is kept: `fixLen d w = w` when `|w| = d`. -/
theorem fixLen_of_length_eq {d : ℕ} {w : List Bool} (h : w.length = d) : fixLen d w = w := by
  rw [fixLen_eq, if_pos h]

/-- A word of the wrong length becomes all-`false`: `fixLen d w = 0^d` when `|w| ≠ d`. -/
theorem fixLen_of_length_ne {d : ℕ} {w : List Bool} (h : w.length ≠ d) :
    fixLen d w = List.replicate d false := by
  rw [fixLen_eq, if_neg h]

/-- `fixLen d w` has `d` bits. -/
theorem length_fixLen (d : ℕ) (w : List Bool) : (fixLen d w).length = d := by
  by_cases h : w.length = d
  · rw [fixLen_of_length_eq h, h]
  · rw [fixLen_of_length_ne h, List.length_replicate]

/-- The empty word becomes all-`false`: `fixLen d [] = 0^d` (for `d = 0` both are empty). -/
theorem fixLen_nil (d : ℕ) : fixLen d [] = List.replicate d false := by
  by_cases h : ([] : List Bool).length = d
  · rw [fixLen_of_length_eq h, ← h, List.length_nil, List.replicate_zero]
  · rw [fixLen_of_length_ne h]

/-- Every word of `d` bits is the string of some `d`-bit vector. -/
theorem exists_ofFn_eq {d : ℕ} {w : List Bool} (h : w.length = d) :
    ∃ x : Fin d → Bool, List.ofFn x = w := by
  cases hd : decodeFin d w with
  | none =>
    rw [decodeFin_eq, dif_pos h] at hd
    exact absurd hd (Option.some_ne_none _)
  | some x => exact ⟨x, ((decodeFin_eq_some_iff d w x).1 hd).symm⟩

/-- **Fixed-length decoding with the all-`false` default is `fixLen`:**
`List.ofFn ((decodeFin d w).getD (zeroBits d)) = fixLen d w`. -/
theorem ofFn_getD_decodeFin (d : ℕ) (w : List Bool) :
    List.ofFn ((decodeFin d w).getD (zeroBits d)) = fixLen d w := by
  cases hd : decodeFin d w with
  | none =>
    have hne : w.length ≠ d := fun h => by
      rw [decodeFin_eq, dif_pos h] at hd
      exact absurd hd (Option.some_ne_none _)
    rw [Option.getD_none, ofFn_zeroBits, fixLen_of_length_ne hne]
  | some x =>
    rw [Option.getD_some, (decodeFin_eq_some_iff d w x).1 hd,
      fixLen_of_length_eq (List.length_ofFn)]

/-- The all-`false` word of a polynomial-time length is polynomial-time:
`z ↦ 0^{|f z|}`. -/
theorem zeros_poly {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    PolyTimeComputable fun z => List.replicate (f z).length false :=
  (EnsembleLemmas.polyTimeComputable_zeros .var hf).congr fun z => by rw [PolyExpr.eval_var]

/-- Equality of two polynomial-time words is a polynomial-time test
(`Complexity.polyTimeComputable_pairEq` on the pair). -/
theorem eq_poly {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g) : PolyTimeComputable fun z => [decide (f z = g z)] :=
  (polyTimeComputable_pairEq.comp' (hf.pairEncode hg)).congr fun z => by
    rw [pairFstD_pairEncode, pairSndD_pairEncode]

/-- Equality of the lengths of two polynomial-time words is a polynomial-time test
(`Complexity.polyTimeComputable_lenEq` on the pair). -/
theorem lenEq_poly {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g) : PolyTimeComputable fun z => [decide ((f z).length = (g z).length)]
        :=
  (polyTimeComputable_lenEq.comp' (hf.pairEncode hg)).congr fun z => by
    rw [pairFstD_pairEncode, pairSndD_pairEncode]

/-- `fixLen` with the length given in unary, `z = ⟨1^d, w⟩ ↦ fixLen d w`, is polynomial-time. -/
theorem fixLen_poly {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g) : PolyTimeComputable fun z => fixLen (f z).length (g z) :=
  (polyTimeComputable_ite (lenEq_poly hg hf) hg (zeros_poly hf)).congr fun z => by
    by_cases h : (g z).length = (f z).length
    · rw [fixLen_of_length_eq h, decide_eq_true h, if_pos rfl]
    · rw [fixLen_of_length_ne h, decide_eq_false h]
      rfl

/-! ### Polynomial lengths selected by an index -/

/-- The length `d i (n)` selected by the index `m = i` (and `0` for `m ≥ k`). -/
def selLen : {k : ℕ} → (Fin k → PolyExpr) → ℕ → ℕ → ℕ
  | 0, _, _, _ => 0
  | _ + 1, d, n, 0 => (d 0).eval n
  | _ + 1, d, n, m + 1 => selLen (fun i => d i.succ) n m

/-- The selected length of an index is its polynomial evaluated:
`selLen d n i = (d i).eval n`. -/
theorem selLen_eq : ∀ {k : ℕ} (d : Fin k → PolyExpr) (n : ℕ) (i : Fin k),
    selLen d n i = (d i).eval n
  | 0, _, _, i => i.elim0
  | _ + 1, d, n, i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rw [Fin.val_succ]
      exact selLen_eq (fun i => d i.succ) n j

/-- A selected index outside the oracle family has length zero.
Together with the finite-index reader this covers every natural index. -/
theorem selLen_of_ge : ∀ {k : ℕ} (d : Fin k → PolyExpr) (n m : ℕ),
    k ≤ m → selLen d n m = 0
  | 0, _, _, _, _ => rfl
  | _ + 1, _, _, 0, h => by omega
  | _ + 1, d, n, m + 1, h =>
      selLen_of_ge (fun i => d i.succ) n m (Nat.le_of_succ_le_succ h)

/-- The selected length in unary, `⟨u, iw⟩ ↦ 1^{selLen d |u| |iw|}`, is polynomial-time (a `k`-way
case split, by induction on `k`). -/
theorem selLen_poly : ∀ {k : ℕ} (d : Fin k → PolyExpr),
    PolyTimeComputable fun z =>
      List.replicate (selLen d (pairFstD z).length (pairSndD z).length) true
  | 0, _ => (polyTimeComputable_const []).congr fun _ => rfl
  | _ + 1, d => by
    have hrest := (selLen_poly (fun i => d i.succ)).comp'
      (polyTimeComputable_pairFstD.pairEncode (polyTimeComputable_tail.comp
          polyTimeComputable_pairSndD))
    have h := polyTimeComputable_ite (polyTimeComputable_isNil.comp polyTimeComputable_pairSndD)
      (StateLoop.unaryPoly_comp (d 0) polyTimeComputable_pairFstD) hrest
    refine h.congr fun z => ?_
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
    cases hz : pairSndD z with
    | nil => rfl
    | cons b w =>
      simp only [List.length_cons, List.drop_one, List.tail_cons]
      rfl

/-- A finite sum of polynomials: `sumPoly d = d 0 + d 1 + ⋯ + d (k - 1)`. -/
def sumPoly : {k : ℕ} → (Fin k → PolyExpr) → PolyExpr
  | 0, _ => .const 0
  | _ + 1, d => .add (d 0) (sumPoly fun i => d i.succ)

/-- `sumPoly` of no polynomials is `0`, and of `k + 1` it is the first plus the rest:
`sumPoly d = .add (d 0) (sumPoly (d ∘ Fin.succ))`. -/
theorem sumPoly_succ {k : ℕ} (d : Fin (k + 1) → PolyExpr) :
    sumPoly d = .add (d 0) (sumPoly fun i => d i.succ) :=
  rfl

/-- Summing an empty family of length polynomials gives the constant zero. -/
theorem sumPoly_zero (d : Fin 0 → PolyExpr) : sumPoly d = .const 0 :=
  rfl

/-- Each summand is below the sum: `(d i).eval n ≤ (sumPoly d).eval n`. -/
theorem eval_le_sumPoly : ∀ {k : ℕ} (d : Fin k → PolyExpr) (i : Fin k) (n : ℕ),
    (d i).eval n ≤ (sumPoly d).eval n
  | 0, _, i, _ => i.elim0
  | _ + 1, d, i, n => by
    rw [sumPoly_succ, PolyExpr.eval_add]
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Nat.le_add_right _ _
    · exact (eval_le_sumPoly (fun i => d i.succ) j n).trans (Nat.le_add_left _ _)

/-- Every selected length is below the sum: `selLen d n m ≤ (sumPoly d).eval n`. -/
theorem selLen_le_sumPoly : ∀ {k : ℕ} (d : Fin k → PolyExpr) (n m : ℕ),
    selLen d n m ≤ (sumPoly d).eval n
  | 0, _, _, _ => Nat.zero_le _
  | _ + 1, d, n, 0 => by
    rw [sumPoly_succ, PolyExpr.eval_add]
    exact Nat.le_add_right _ _
  | _ + 1, d, n, m + 1 => by
    rw [sumPoly_succ, PolyExpr.eval_add]
    exact (selLen_le_sumPoly (fun i => d i.succ) n m).trans (Nat.le_add_left _ _)

/-- The bits that one entry `⟨1^i, ⟨x, y⟩⟩` adds to an encoded log, at most
`4k + 10 + 4 Σ din + 2 Σ dout`. -/
def entryPoly (din dout : Fin k → PolyExpr) : PolyExpr :=
  .add (.const (4 * k + 10)) (.add (.mul (.const 4) (sumPoly din)) (.mul (.const 2) (sumPoly dout)))

/-- The defining equation of `entryPoly`. -/
theorem entryPoly_eq (din dout : Fin k → PolyExpr) : entryPoly din dout =
    .add (.const (4 * k + 10)) (.add (.mul (.const 4) (sumPoly din)) (.mul (.const 2) (sumPoly
        dout))) :=
  rfl

/-- **The entry bound:** a log entry of the bit-string oracles adds at most `entryPoly` bits to an
encoded log, `2 |encodeEntry e| + 2 ≤ entryPoly(n)`. -/
theorem entry_le_entryPoly (din dout : Fin k → PolyExpr) (n : ℕ)
    (e : Σ i, (bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n)).dom i ×
      (bitSpec (fun i => (din i).eval n) (fun i => (dout i).eval n)).rng i) (dα : ℕ) :
    2 * ((bitCodec (fun i => (din i).eval n) (fun i => (dout i).eval n) dα).encodeEntry e).length
      + 2 ≤ (entryPoly din dout).eval n := by
  rw [bitCodec_encodeEntry, length_pairEncode, length_pairEncode, List.length_replicate,
    List.length_ofFn, List.length_ofFn, entryPoly_eq]
  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
  have h1 := e.1.isLt
  have h2 := eval_le_sumPoly din e.1 n
  have h3 := eval_le_sumPoly dout e.1 n
  omega

/-- The parameter is at most the length of the raw layout `⟨⟨⟨1^n, y⟩, α⟩, r⟩`. -/
theorem le_length_layout (n : ℕ) (y α r : List Bool) :
    n ≤ (NUPPT.layout (List.replicate n true) y α r).length := by
  rw [NUPPT.layout_eq, length_pairEncode, length_pairEncode, length_pairEncode,
    List.length_replicate]
  omega

/-! ### The canonical decoder -/

/-- The query test of the canonical decoder: `w = ⟨[false], ⟨iw, xw⟩⟩` with `iw = 1^i`, `i < k`
and `|xw| = din i (n)`, tested by re-encoding and comparing. -/
def canonQ (din : Fin k → PolyExpr) (n : ℕ) (w : List Bool) : Bool :=
  decide (w = pairEncode [false] (pairEncode (pairFstD (pairSndD w)) (pairSndD (pairSndD w)))) &&
    decide (pairFstD (pairSndD w) = List.replicate (pairFstD (pairSndD w)).length true) &&
    decide ((pairFstD (pairSndD w)).length < k) &&
    decide ((pairSndD (pairSndD w)).length = selLen din n (pairFstD (pairSndD w)).length)

/-- `canonQ din n w` is the conjunction of the four tests (its defining equation). -/
theorem canonQ_eq (din : Fin k → PolyExpr) (n : ℕ) (w : List Bool) :
    canonQ din n w =
      (decide (w = pairEncode [false] (pairEncode (pairFstD (pairSndD w)) (pairSndD (pairSndD w))))
        && decide (pairFstD (pairSndD w) = List.replicate (pairFstD (pairSndD w)).length true)
        && decide ((pairFstD (pairSndD w)).length < k)
        && decide ((pairSndD (pairSndD w)).length = selLen din n (pairFstD (pairSndD w)).length)) :=
  rfl

/-- The output test of the canonical decoder: `w = ⟨[true], a⟩` with `|a| = dα`. -/
def canonR (dα : ℕ) (w : List Bool) : Bool :=
  decide (w = pairEncode [true] (pairSndD w)) && decide ((pairSndD w).length = dα)

/-- `canonR dα w` is the conjunction of the two tests (its defining equation). -/
theorem canonR_eq (dα : ℕ) (w : List Bool) :
    canonR dα w = (decide (w = pairEncode [true] (pairSndD w)) && decide ((pairSndD w).length = dα))
        :=
  rfl

/-- **The canonical decoder** at parameter `n` with `dα`-bit outputs: a canonical query or output
word is kept, every other word becomes the canonical word `⟨[true], 0^dα⟩` of the default. -/
def canonWord (din : Fin k → PolyExpr) (n dα : ℕ) (w : List Bool) : List Bool :=
  if canonQ din n w || canonR dα w then w else pairEncode [true] (List.replicate dα false)

/-- `canonWord din n dα w = if canonQ din n w || canonR dα w then w else ⟨[true], 0^dα⟩`. -/
theorem canonWord_eq_ite (din : Fin k → PolyExpr) (n dα : ℕ) (w : List Bool) :
    canonWord din n dα w =
      if canonQ din n w || canonR dα w then w else pairEncode [true] (List.replicate dα false) :=
  rfl

/-- **The canonical decoder is the canonical word of the decoded move:** for every word `w` (and
any answer lengths `dout`), `canonWord din n dα w = encodeBitMove (decodeBitMove w)` at the
evaluated lengths.

**Proof sketch.** Three cases. A canonical query word `⟨[false], ⟨1^i, x⟩⟩` passes the query test
(the index is below `k` and `|x| = din i (n)` by `selLen_eq`) and decodes to its query, whose
canonical word it is (`decodeBitMove_query`). A canonical output word passes the output test and
decodes to its output (`decodeBitMove_ret`). Any other word fails both tests: a word passing the
query test is, after re-encoding, the canonical word of the query at index `|iw|` with payload
`xw` (`exists_ofFn_eq`), and one passing the output test is a canonical output word. So it becomes
`⟨[true], 0^dα⟩`, the canonical word of the default (`decodeBitMove_of_not_canonical`,
`ofFn_zeroBits`). -/
theorem canonWord_eq (din : Fin k → PolyExpr) (dout : Fin k → ℕ) (n dα : ℕ) (w : List Bool) :
    canonWord din n dα w =
      encodeBitMove (fun i => (din i).eval n) dout dα
        (decodeBitMove (fun i => (din i).eval n) dout dα w) := by
  by_cases hq : ∃ (i : Fin k) (x : Fin ((din i).eval n) → Bool),
      w = pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x))
  · obtain ⟨i, x, rfl⟩ := hq
    rw [decodeBitMove_query, encodeBitMove_query, canonWord_eq_ite, if_pos]
    rw [canonQ_eq]
    simp only [pairSndD_pairEncode, pairFstD_pairEncode, List.length_replicate, List.length_ofFn,
      selLen_eq, i.isLt, decide_true, Bool.and_true, Bool.true_or]
  by_cases hr : ∃ a : Fin dα → Bool, w = pairEncode [true] (List.ofFn a)
  · obtain ⟨a, rfl⟩ := hr
    rw [decodeBitMove_ret, encodeBitMove_ret, canonWord_eq_ite, if_pos]
    rw [canonR_eq]
    simp only [pairSndD_pairEncode, List.length_ofFn, decide_true, Bool.and_true, Bool.or_true]
  have hq' : ∀ (i : Fin k) (x : Fin ((din i).eval n) → Bool),
      w ≠ pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x)) :=
    fun i x h => hq ⟨i, x, h⟩
  have hr' : ∀ a : Fin dα → Bool, w ≠ pairEncode [true] (List.ofFn a) := fun a h => hr ⟨a, h⟩
  rw [decodeBitMove_of_not_canonical hq' hr', encodeBitMove_ret, ofFn_zeroBits, canonWord_eq_ite,
    if_neg]
  rw [Bool.or_eq_true, not_or]
  constructor
  · intro h
    rw [canonQ_eq] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hw, hiw⟩, hlt⟩, hx⟩ := h
    let i : Fin k := ⟨(pairFstD (pairSndD w)).length, hlt⟩
    have hx' : (pairSndD (pairSndD w)).length = (din i).eval n := by
      rw [hx, ← selLen_eq]
    obtain ⟨x, hxe⟩ := exists_ofFn_eq hx'
    refine hq' i x ?_
    rw [hxe]
    exact hw.trans (by rw [← hiw])
  · intro h
    rw [canonR_eq] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hw, hlen⟩ := h
    obtain ⟨a, ha⟩ := exists_ofFn_eq hlen
    exact hr' a (by rw [ha]; exact hw)

/-- The canonical decoder as a function of `⟨1^n, ⟨1^dα, w⟩⟩`. -/
def canonFun (din : Fin k → PolyExpr) (z : List Bool) : List Bool :=
  canonWord din (pairFstD z).length (pairFstD (pairSndD z)).length (pairSndD (pairSndD z))

/-- On every raw word the canonical decoder reads its three inputs through
the total pair projections. -/
theorem canonFun_def (din : Fin k → PolyExpr) (z : List Bool) :
    canonFun din z =
      canonWord din (pairFstD z).length (pairFstD (pairSndD z)).length
        (pairSndD (pairSndD z)) :=
  rfl

/-- The canonical decoder reads `n` and `dα` in unary:
`canonFun din ⟨1^n, ⟨1^dα, w⟩⟩ = canonWord din n dα w`. -/
theorem canonFun_eq (din : Fin k → PolyExpr) (n dα : ℕ) (w : List Bool) :
    canonFun din (pairEncode (List.replicate n true) (pairEncode (List.replicate dα true) w)) =
      canonWord din n dα w := by
  rw [canonFun, pairFstD_pairEncode, pairSndD_pairEncode, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate, List.length_replicate]

/-- **The canonical decoder is polynomial-time:** each test is a comparison of polynomial-time
words (`eq_poly`, `lenEq_poly`, `Complexity.StateLoop.lenLe_comp`, `selLen_poly`), and the
output a branch (`Complexity.polyTimeComputable_ite`). -/
theorem canonFun_poly (din : Fin k → PolyExpr) : PolyTimeComputable (canonFun din) := by
  have hu := polyTimeComputable_pairFstD
  have hrl := polyTimeComputable_pairFstD.comp' polyTimeComputable_pairSndD
  have hw := polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD
  have hrest := polyTimeComputable_pairSndD.comp' hw
  have hiw := polyTimeComputable_pairFstD.comp' hrest
  have hxw := polyTimeComputable_pairSndD.comp' hrest
  have h1 := eq_poly hw ((polyTimeComputable_const [false]).pairEncode (hiw.pairEncode hxw))
  have h2 := eq_poly hiw (polyTimeComputable_unary.comp' hiw)
  have h3 : PolyTimeComputable fun z =>
      [decide ((true :: pairFstD (pairSndD (pairSndD (pairSndD z)))).length ≤
        (List.replicate k true).length)] :=
    StateLoop.lenLe_comp (polyTimeComputable_const _) ((StateLoop.cons_poly true).comp' hiw)
  have h4 := lenEq_poly hxw ((selLen_poly din).comp' (hu.pairEncode hiw))
  have hQ := polyTimeComputable_and (polyTimeComputable_and (polyTimeComputable_and h1 h2) h3) h4
  have h5 := eq_poly hw ((polyTimeComputable_const [true]).pairEncode hrest)
  have h6 := lenEq_poly hrest hrl
  have hR := polyTimeComputable_and h5 h6
  have h := polyTimeComputable_ite (polyTimeComputable_or hQ hR) hw
    ((polyTimeComputable_const [true]).pairEncode (zeros_poly hrl))
  refine h.congr fun z => ?_
  rw [canonFun, canonWord_eq_ite, canonQ_eq, canonR_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate, List.length_cons,
    Nat.succ_le_iff]

/-! ### Activation loops -/

/-- The step of an activation loop: the second component of the activation's result. -/
def actStep (act : List Bool → List Bool) (w : List Bool) : List Bool :=
  pairSndD (act w)

/-- `actStep act w = pairSndD (act w)`. -/
theorem actStep_eq (act : List Bool → List Bool) (w : List Bool) :
    actStep act w = pairSndD (act w) :=
  rfl

/-- The stopping test of an activation loop: the activation's result is tagged `[true]`. -/
def actAcc (act : List Bool → List Bool) (w : List Bool) : Bool :=
  decide (pairFstD (act w) = [true])

/-- `actAcc act w = decide (pairFstD (act w) = [true])`. -/
theorem actAcc_eq (act : List Bool → List Bool) (w : List Bool) :
    actAcc act w = decide (pairFstD (act w) = [true]) :=
  rfl

/-- **The activation loop:** `GGMRed.stateLoopFun` whose round is one activation `act` on the
state word `⟨x, s⟩`, returning `⟨[false], s'⟩` to continue with the state `s'` or `⟨[true], o⟩` to
stop with the output `o`; at most `R|x|` rounds, states bounded by `B|x|`. -/
def actLoop (start act : List Bool → List Bool) (R B : PolyExpr) : List Bool → List Bool :=
  GGMRed.stateLoopFun start (actStep act) (actAcc act) (actStep act) R B

/-- `actLoop start act R B = GGMRed.stateLoopFun start (actStep act) (actAcc act) (actStep act) R
B`.
-/
theorem actLoop_eq (start act : List Bool → List Bool) (R B : PolyExpr) :
    actLoop start act R B =
      GGMRed.stateLoopFun start (actStep act) (actAcc act) (actStep act) R B :=
  rfl

/-- An activation loop with polynomial-time start and activation is polynomial-time
(`GGMRed.stateLoopFun_poly`). -/
theorem actLoop_poly {start act : List Bool → List Bool} (hstart : PolyTimeComputable start)
    (hact : PolyTimeComputable act) (R B : PolyExpr) : PolyTimeComputable (actLoop start act R B) :=
  GGMRed.stateLoopFun_poly hstart (polyTimeComputable_pairSndD.comp' hact)
    (eq_poly (polyTimeComputable_pairFstD.comp' hact) (polyTimeComputable_const [true]))
    (polyTimeComputable_pairSndD.comp' hact) R B

/-- **The run invariant of an activation loop:** on input `x`, the state after `t` rounds is `S`,
no earlier round stopped, and the states so far are bounded by `B|x|`. -/
def RunsTo (start act : List Bool → List Bool) (B : PolyExpr) (x : List Bool) (t : ℕ)
    (S : List Bool) : Prop :=
  (∀ i < t, actAcc act (pairEncode x (StateLoop.orbit start (actStep act) x i)) = false) ∧
    (∀ i ≤ t, (StateLoop.orbit start (actStep act) x i).length ≤ B.eval x.length) ∧
    StateLoop.orbit start (actStep act) x t = S

/-- `RunsTo` is the conjunction of its three clauses (its defining equation). -/
theorem runsTo_iff (start act : List Bool → List Bool) (B : PolyExpr) (x : List Bool) (t : ℕ)
    (S : List Bool) :
    RunsTo start act B x t S ↔
      (∀ i < t, actAcc act (pairEncode x (StateLoop.orbit start (actStep act) x i)) = false) ∧
        (∀ i ≤ t, (StateLoop.orbit start (actStep act) x i).length ≤ B.eval x.length) ∧
        StateLoop.orbit start (actStep act) x t = S :=
  Iff.rfl

/-- The run starts at `start x`, if that state is within the bound. -/
theorem runsTo_zero {start act : List Bool → List Bool} {B : PolyExpr} {x : List Bool}
    (h : (start x).length ≤ B.eval x.length) : RunsTo start act B x 0 (start x) := by
  refine ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => ?_, StateLoop.orbit_zero _ _ _⟩
  rw [Nat.le_zero.1 hi, StateLoop.orbit_zero]
  exact h

/-- **A continuing round:** if the activation on `⟨x, S⟩` continues with `S'` within the bound,
the run reaches `S'` one round later. -/
theorem runsTo_succ {start act : List Bool → List Bool} {B : PolyExpr} {x : List Bool} {t : ℕ}
    {S S' : List Bool} (h : RunsTo start act B x t S) (hact : act (pairEncode x S) = pairEncode
        [false] S')
    (hS' : S'.length ≤ B.eval x.length) : RunsTo start act B x (t + 1) S' := by
  obtain ⟨hf, hb, hS⟩ := h
  have horb : StateLoop.orbit start (actStep act) x (t + 1) = S' := by
    rw [StateLoop.orbit_succ, hS, actStep_eq, hact, pairSndD_pairEncode]
  refine ⟨fun i hi => ?_, fun i hi => ?_, horb⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact hf i hi
    · rw [hS, actAcc_eq, hact, pairFstD_pairEncode]
      rfl
  · rcases Nat.lt_or_eq_of_le hi with hi | rfl
    · exact hb i (Nat.lt_succ_iff.1 hi)
    · rw [horb]
      exact hS'

/-- **A stopping round:** if the activation on `⟨x, S⟩` stops with the output `o` at a round
`t ≤ R|x|`, the loop returns `o` (`GGMRed.stateLoopFun_eval`). -/
theorem runsTo_stop {start act : List Bool → List Bool} {R B : PolyExpr} {x : List Bool} {t : ℕ}
    {S o : List Bool} (h : RunsTo start act B x t S) (hact : act (pairEncode x S) = pairEncode
        [true] o)
    (ht : t ≤ R.eval x.length) : actLoop start act R B x = o := by
  obtain ⟨hf, hb, hS⟩ := h
  rw [actLoop_eq, GGMRed.stateLoopFun_eval _ _ _ _ R B x t ht hb hf, hS, actStep_eq, hact,
    pairSndD_pairEncode]
  rw [hS, actAcc_eq, hact, pairFstD_pairEncode]
  rfl

/-! ### Machine glue -/

/-- **A raw function with a seed as data is a machine.** For a polynomial-time `F`, an advice
family of polynomial length and a seed length `p`, there is a machine `B` and, at every
parameter, a bijection `φ` from (seed, `A`'s coins) to `B`'s coins such that `B` on the argument
`y` with coins `φ (ω, r)` returns `F` of the raw layout `⟨⟨⟨1^n, ⟨y, ω⟩⟩, advice n⟩, r⟩`.

**Proof sketch.** `B` is `NUPPT.exists_split` with `p` of `NUPPT.ofPolyTime hF A.coins adv advice`,
so its coin polynomial is `p + A.coins` (`coins_ofPolyTime`, `coinLen_eq`, `PolyExpr.eval_add`).
`φ` appends the seed and the coins (`Fin.appendEquiv`) and transports along that length
equation; its string is `ω ++ r` (`List.ofFn_fin_append`, `List.ofFn_congr`), which the split
cuts back into `ω` and `r` (`runAtL_ofPolyTime`). -/
theorem exists_splitMachine (A : NUPPT) {F : List Bool → List Bool} (hF : PolyTimeComputable F)
    (adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n)
    (p : PolyExpr) :
    ∃ B : NUPPT, ∀ n : ℕ, ∃ φ : (Fin (p.eval n) → Bool) × A.Coins n ≃ B.Coins n,
      ∀ (y : List Bool) (ω : Fin (p.eval n) → Bool) (r : A.Coins n),
        B.runAt n y (φ (ω, r)) =
          F (NUPPT.layout (List.replicate n true) (pairEncode y (List.ofFn ω)) (advice n)
            (List.ofFn r)) := by
  obtain ⟨B, hBc, -, hB⟩ := NUPPT.exists_split (NUPPT.ofPolyTime hF A.coins adv advice hα) p
  refine ⟨B, fun n => ?_⟩
  have hlen : p.eval n + A.coinLen n = B.coinLen n := by
    rw [NUPPT.coinLen_eq, NUPPT.coinLen_eq, hBc, PolyExpr.eval_add, NUPPT.coins_ofPolyTime]
  refine ⟨(Fin.appendEquiv (p.eval n) (A.coinLen n)).trans
    (Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)), fun y ω r => ?_⟩
  have hofFn : List.ofFn (((Fin.appendEquiv (p.eval n) (A.coinLen n)).trans
      (Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool))) (ω, r)) =
      List.ofFn ω ++ List.ofFn r := by
    rw [← List.ofFn_fin_append, List.ofFn_congr hlen (Fin.append ω r)]
    rfl
  rw [NUPPT.runAt_eq, hofFn, hB, List.take_left' (List.length_ofFn), List.drop_left'
    (List.length_ofFn), NUPPT.runAtL_ofPolyTime, NUPPT.layout_eq, NUPPT.advInput_eq]

end TCSlib.Cryptography.Games.EffFill
