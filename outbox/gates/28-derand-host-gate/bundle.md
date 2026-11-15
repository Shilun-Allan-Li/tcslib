## ===== briefs/pass-shelat-ch5-8/gates/28-derand-host/pack.md =====

# Gate 28 · The seed-majority enumeration host for derandomization (derand host, statement)

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews).

- **PR:** draft [PR #312](https://github.com/Shilun-Allan-Li/tcslib/pull/312) at
  `8972fb4ef15fa3d4e3df37d6aa8674408835593d` (branch `stmt/pass-shelat-derand-host`, tree
  `ba544f9ca0d80ff12644128a2cc32a94d6b5f709`).
- **Target and base:** the PR targets `cryptography/pass-shelat-ch2-4` on base
  `013119f006af40d03b88b0fc2d9b453cf0a9b348` (the merge base; GitHub shows the branch tip at opening, `b12a12f2`, a
  records commit). The two commits from the base to the records tip `41e3cd2a6b637ed10c6782b5f3c68212f9f77b65`
  (`b12a12f2`, `41e3cd2a`) touch records only: `PassShelatChapter5-8Plan.md` and the two evidence folders
  `maintainer/stmt-b1-2026-11-15/` and `maintainer/stmt-derand-2026-11-15/`. The diff
  `origin/cryptography/pass-shelat-ch2-4...8972fb4e` equals `013119f0..8972fb4e` byte for byte (`pr.diff.txt`).
- **Commits:** 1, by the maintainer (author Claude): `8972fb4e` "Statement: the seed-majority enumeration host
  (derand, PS10 Thm 180.1)".
- **Scope:** a **statement audit** of a *host contract*. Seyoon ruled on 2026-11-14 that `derand`
  (`Randomness.bpp_subset_dtime_subexp`, [PS10, §8.2, Theorem 180.1]) is **held**: the deterministic counting/majority
  enumeration host it needs is first stated, sorried, by the maintainer in a statement PR with its own gate, and only
  then is `derand` dispatched. This PR is that statement. It adds no `def`.
- **Sources:** [PS10] §8.2, Theorem 180.1 (book p. 180), step 4 of its proof; [AB09] S. Arora and B. Barak,
  *Computational Complexity*, 2009, §7.1, p. 126 (`BPP ⊆ EXP` by enumerating the random strings) and Claim 2.4.

## What changed

The PR touches 2 Lean files (167 insertions, 0 deletions). Paths are under `TCSlib/Complexity/`.

| File | Status | Lines | SHA-256 at head |
|---|---|---:|---|
| `Randomized/SeedMajority.lean` | new | 163 | `3f6758b1…` |
| `Randomized.lean` (facade) | modified: one import and one `## Contents` entry (3 lines) | 206 → 210 | `bfefe641…` |

The new module imports `ClassP/P`, `ClassNP/PolyTime`, `TuringMachine/Encoding` and `Randomized/Classes`. It has two
public theorems and nothing else:

```lean
open Classical in
theorem Complexity.seedMajority_mem_DTIME {V : Language Bool} (hV : V ∈ P) (w : ℕ → ℕ)
    (hw : PolyTimeComputable fun x => List.replicate (w x.length) true) :
    ∃ e : ℕ,
      {x : List Bool | 2 ^ w x.length <
          2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
            pairEncode x (List.ofFn u) ∈ V).card} ∈
        DTIME fun n => 2 ^ w n * (n + 1) ^ e := by
  sorry   -- the contract; the only sorry

theorem Randomized.half_lt_randProb_iff (m : ℕ) (A : List Bool → Prop) [DecidablePred A] :
    1 / 2 < randProb m A ↔
      2 ^ m < 2 * (univ.filter fun r : Fin m → Bool => A (List.ofFn r)).card   -- proved
```

`DTIME T = {L | ∃ c M, M.DecidesInTime L (fun n => c * T n)}` (`ClassP/DTIME.lean`), so the one membership carries
correctness (some machine decides exactly the strict-majority language; ties reject) and the time bound
`c · 2^{w(n)} · (n+1)^e`.

The maintainer's design choices, disclosed for this gate (PR description; `pr-body.md` § Design and § Decisions):
1. **Existential machine.** The contract is a class membership. No `def`, so no sorried definition and no reader owed;
   consumers read it through `DTIME.mono`, `Randomized.DTIME_const_mul_subset` and `half_lt_randProb_iff`.
2. **Generality.** The test is any `V ∈ P` read on `pairEncode x u` (the convention of `Randomized.polyTimeModel`), not
   a decider of arbitrary time on `x ++ u`; the width is any `w` whose unary word is polynomial-time; majority is
   strict, with no general threshold; only the `DTIME` form, with no machine-level `DecidesInTime` contract.
3. **No head-envelope (space) clause:** a decision-layer host, as `exists_proj_decider` is.
4. **Placement:** the shared `Complexity/Randomized` layer, not `derand`'s helper directory (policy §1, a second
   prospective consumer `BPP ⊆ EXP` [AB09, p. 126], and Complexity does not import Cryptography).
5. **Relatives not reused:** `Complexity.exists_proj_decider` (any-verdict, fixed width `C(n+1)^c`, test on `x ++ u`,
   private engine) and the polynomial block-majority tests.
6. **Registry row H17** for `machine-library-design.md` §14 is drafted in `pr-body.md` and not yet entered.

## Rulings and records in force

- **derand held; host contract first (Seyoon, 2026-11-14,** decision-log row "Rulings (Seyoon) on the staged
  fills"**):** the deterministic counting/majority enumeration host's contract is first stated (sorried) by the
  maintainer in a statement PR with its own gate; then `derand` is dispatched.
- **Derand fill pre-approvals (Seyoon, 2026-11-15,** row "derand host statement PR"**), for the later fill, not for
  this PR:**
  1. harvest one public generic-fuel `computesFunInTime_find` (with its contract) into the frozen
     `Complexity/Randomized/Build/IterateFind.lean`, reusing its private helpers in place;
  2. add `mem_DTIME_iff` (by `Iff.rfl`, with a formula docstring) beside `DTIME` in the frozen shared
     `ClassP/DTIME.lean`, its downstream rebuilt at review.

  The same row says the derand brief is updated after this gate: step 4 and checkpoint 1 consume the contract, and the
  order and roots are regenerated.
- **The derand brief** `fills/derand/issued-r1/brief.md` (in `verification.zip`, `records/`) is the consumer's issued
  brief. Its checkpoint 1 asked for a scope request for "a deterministic machine that runs a decider on `x ++ u` for
  every seed `u` of width `w` and accepts iff more than half accept, within `b · 2^w · (T(n + w) + poly)`". The stated
  contract specializes this to a `P` test on `pairEncode x u`; see question 3.
- **Policy §1, *Hosts come first*:** a host is never built `private` inside the proof that first needs it; its public
  contract is designed, statement-gated and placed in the shared construction layer first, generic in the parts its
  consumers vary, with time and space (head-envelope) clauses. The host registry is `machine-library-design.md` §14
  (rows H14 clean-module host, H16 counted word loop at the FP layer, in `verification.zip`).
- **Standing rules:** Rule 10; formula docstrings with `[PS10 …]`/`[AB09 …]` tags and a `**Proof sketch.**` (policy
  §§2–3); the #305 facade rule; lint baseline **92 FAIL / 101 WARN** on `TCSlib/Cryptography` with no new line (the
  PR also reports `TCSlib/Complexity`, 25 / 391); lines of at most 100 characters.

## What is frozen

Every file other than the new module and the facade's import and `## Contents` lines, in particular
`Cryptography/Randomness/Derandomization.lean` (`bpp_subset_dtime_subexp`, `subexpBound`), `ClassP/DTIME.lean`,
`Randomized/Classes.lean` (`randProb`, `randProb_eq`), `Randomized/QuasiPolyHierarchy.lean`
(`DTIME_const_mul_subset`), `Randomized/Build/IterateFind.lean` and `ClassNP/EXP.lean`: byte-identical to the base
(check with `pr.diff.txt`). The two derand pre-approvals above are not exercised here.

## Questions for the audit

1. **Is the contract true?** Including:
   - **ties:** `2^w = 2 · count` rejects; is that the intended strict majority, and is it what Theorem 180.1 needs (its
     `1/12` margin keeps acceptance probabilities away from `1/2`)?
   - **`w = 0`** (and `w x.length = 0` at some lengths): one seed, the empty word; the language is
     `{x | pairEncode x [] ∈ V}` at those lengths and the bound is `(n+1)^e`;
   - **small `n`:** `n = 0`, where the bound is `2^{w 0}`; and `DTIME_eq_empty_of_exists_zero` (the bound is never 0
     here);
   - **the time:** `2^{w(n)}` rounds, each a polynomial-time step on a state of length `O(n + w(n))`, with
     `w(n) ≤ C(n+1)^c` from `hw` (`PolyTimeComputable.output_length_le`); is `c · 2^{w(n)} · (n+1)^e` attainable on
     every input, including the cost of computing `1^{w(|x|)}` and of the final comparison?
   - the decision layer: `DecidesInTime` requires output exactly `[decide (x ∈ L)]` within `c · T(|x|)` steps on every
     `x : List Bool`.
2. **Is it sufficient for Theorem 180.1?** The PR description (`pr-body.md` § "Theorem 180.1 from the contract and the
   PRG hypothesis") gives a six-step paper proof; the module docstring's § Consumers gives the instantiation. Check:
   - the test `V'' = {⟨x, u⟩ | if |x| < n₀ then ⟨x, u⟩ ∈ V₁ else ⟨x, F'(u)↾m(|x|)⟩ ∈ V₁}` is in `P`
     (`preimage_mem_P`, Boolean closure, `PolyTimeComputable.pairEncode`, prefix truncation), with `V₁` the
     `some true`-set of the `polyTimeModel` verifier;
   - the width `w(n) = if n < n₀ then m(n) else ℓ(n)` (`ℓ(n)` the least `t` with `n ≤ t^d`) has a polynomial-time unary
     word; `n₀` is obtained non-constructively from PRG security, which is harmless for a fixed function `w` — is it?
   - `L` equals the majority language: below `n₀` with the true coins (acceptance `≥ 2/3` or `≤ 1/3`), from `n₀` on with
     gap at most `1/12` (`≥ 7/12` or `≤ 5/12`); `half_lt_randProb_iff` converts;
   - the bound `2^{w n}(n+1)^e ≤ c · subexpBound ε n` for all `n`, the finite exceptions absorbed into `c`
     (`subexpBound_pos`), then `DTIME.mono` and `DTIME_const_mul_subset`;
   - whether step 2 (bad input lengths to bad seed lengths, advice `|x| ≤ s^d`, `verifier_toNUPPT`,
     `NUPPT.exists_withAdvice(On)`, `randProb_eq_uprob`, `PRG.secure_iff`) is consistent with the frozen sketch of
     `bpp_subset_dtime_subexp`.

   `probes/ConsumerProbe.lean` checks only the last step (from a pointwise bound to `DTIME T`), sealed.
3. **Is the generality appropriate?**
   - A `P` test on `pairEncode x u`, versus the brief's decider of arbitrary time on `x ++ u`: is `P` enough for both
     consumers (derand's `V''` and `BPP ⊆ EXP` by coin enumeration with `w = polyLen a k`), and is `pairEncode` the
     right convention (it is `polyTimeModel`'s)?
   - Strict majority only, with no general threshold: does any foreseeable consumer need `t · 2^w < count`, or the
     count itself?
   - The `DTIME` form only, with no machine-level contract: does any consumer need to compose the host's machine (e.g.
     as a clean module inside a larger machine), which a `DTIME` membership cannot provide?
   - Is the width hypothesis `hw` the right one (input-length dependence only; the unary word rather than a binary
     one)?
4. **Is it placed in the shared layer, and is it Rule-10 clean?**
   - Policy §1 asks for the shared *construction* layer and for time and space (head-envelope) clauses. Is
     `Complexity/Randomized/` the right home (rather than `TuringMachine/Build/` or beside `ClassNP/EXP.lean`), and is
     the missing space clause acceptable for a decision-layer contract (precedent `exists_proj_decider`)?
   - Must the registry row H17 be entered in `machine-library-design.md` §14 before this PR merges, or with it?
   - Rule 10: `half_lt_randProb_iff` reads `randProb` only through `randProb_eq`; the statement uses `DTIME`, `P`,
     `PolyTimeComputable`, `pairEncode` and the `Finset` count as atoms. The evidence has a whole-file seal of the new
     module and a consumer probe, each with a paired control.
   - Nearest relatives: `exists_proj_decider` (`ClassNP/EXP.lean`), the block-majority tests
     (`ClassNP/PolyTimeBlockMajority.lean`), H16 `BinArith.forLoop` (`ClassP/BinaryArith/Loops.lean`, a counted loop
     with one round per counter letter) and `IterateFind.polyTimeComputable_find`. Is any of them, or a published
     generalization of one, the contract that should be stated instead?
5. **Is it provable on the stated route?** The module docstring's § Route: a state loop `⟨x, ⟨i, a⟩⟩`; the
   result-bearing combinator `Turing.FinTM.exists_loopFindTM` over the clean-module host with fuel
   `Nat.bits (2^{w(|x|)})`, bound `c (T(n) + 1)(R(n) + 2)`; the count through `i ↦ word_w(i)`; the normal form.
   - `evidence/probes/RouteAxioms.log`: 26 route lemmas, standard axioms only; the route avoids the admitted
     `loopHostTM_*` and `timedCondTM_*` specs.
   - Is the exponential fuel compatible with `exists_loopFindTM`'s contract (its fuel and time parameters, and the
     polynomial `T` of each round), and with the private `IterateFind` helpers (`Inv`, `verdictWord`, `stepWord`,
     `outWord`, `final_bound`), given the pre-approved harvest of a generic-fuel `computesFunInTime_find`?
   - Is introducing a `DTIME` membership possible without reading `DTIME`'s body, given the pre-approved
     `mem_DTIME_iff`?
   - The size estimate is 0.9–1.6k lines for the host; is it plausible?
6. **Docstrings and attribution.** Module docstring (formal reading, `## Main results`, consumers, design, route,
   `## References`) and the two theorem docstrings: formulas, `[PS10 …]`/`[AB09 …]` tags, the `**Deviation.**` and the
   contract's `**Proof sketch.**`.

## Known dispositions (not findings)

- **The facade edit** (one import, one `## Contents` entry) is the #305 facade rule, not a frozen-file change.
- **The host's proof is out of scope.** The gate asks whether the contract is true, sufficient, appropriately general,
  well placed and provable on the stated route.
- **Not exercised here:** the two derand pre-approvals (the `IterateFind` harvest and `mem_DTIME_iff`); the H17
  registry row (drafted only); the derand brief update.
- **Two PR texts.** The GitHub description of #312 is a shortened rewrite of the evidence's `pr-body.md` (in
  `verification.zip`, `records/…/stmt-derand-2026-11-15/pr-body.md`, byte-identical to the ZIP entry). The paper proof,
  the eight decisions for Seyoon and the draft H17 row are in full only in `pr-body.md`.
- **The evidence build** checked 63 modules in an olean tree whose base is source `eff2dcd0`: the new module, its
  facade, the 51 Cryptography modules changed between `eff2dcd0` and the PR base and their downstream, root `TCSlib`
  and `audits/pass-shelat/Checks`. `build/results.jsonl` has 64 lines: 63 module rows and a final `done` marker.

### Wording noted by the staging (please rate)

- The module docstring says "the proof is a separate fill"; the PR description says "The `derand` fill will then
  prove both the host and the theorem", and the 2026-11-15 pre-approvals are given to the derand fill. Which unit
  proves the contract is not stated the same way in the three places.

## Also check

- The `sorry` is the only one in the PR, at `SeedMajority.lean:154` (`seedMajority_mem_DTIME`); `half_lt_randProb_iff`
  uses the three standard axioms (`evidence/probes/ConsumerProbe.log`).
- Every line of the two files is at most 100 characters (`source-head.json`; `evidence/lint/widths.txt`).
- `open Classical in` on the contract: is the decidability instance of the `Finset.filter` the one a consumer obtains
  (the consumer probe rewrites with `half_lt_randProb_iff`, whose `[DecidablePred A]` is explicit)?
- Namespaces: the contract is in `Complexity`, the reader in `Randomized`, matching `DTIME` and `randProb`.

## Evidence

`verification.zip` (45 entries; its `SHA256SUMS` lists every other entry, `PROVENANCE.txt` maps each to its source)
holds byte-identical originals from records `41e3cd2a`:
- `stmt-derand-evidence.zip` (SHA-256 `aace4d2a…`, 107 file entries = the 106 manifest paths under `stmt-derand/` plus
  that folder's `SHA256SUMS`, byte-identical to the manifest) and its manifest `evidence-SHA256SUMS`;
- `records/`: the evidence's `PROVENANCE.txt` and `pr-body.md` (as beside the ZIP), the decision log, the duplication
  ledger, `machine-library-design.md` (§14, host registry) and the derand issue package `fills/derand/issued-r1/`;
- `evidence/`: byte copies of the ZIP entries cited here:
  - `build/order.txt`, `build/results.jsonl`, `build/mods/*.log` (4 of the 63): 63/63 rc 0, 0 errors (both
    `error:` and `error(` forms counted, G26-N1); the only `sorry` warning is `SeedMajority.lean:154:8`;
  - `probes/RouteAxioms.lean`/`.log` (route lemmas' axioms); `probes/SealSeedMajority.lean`/`.log` (whole-file seal:
    `randProb`, `DTIME`, `P`, `PolyTimeComputable`, `pairEncode` local irreducible; rc 0);
    `SealSeedMajorityControl` / `UnsealedSeedMajorityControl` (a control reading `randProb` through its body fails
    sealed exactly once, line 172, and passes unsealed); `ConsumerProbe` / `ConsumerProbeUnsealed` (the last step of
    derand through readers only, sealed; its control builds `DTIME` membership through the body and fails exactly
    once sealed; all pass unsealed);
  - `lint/linediff.txt` (Cryptography 92/101 and Complexity 25/391 at base and head, 0 new and 0 gone lines),
    `lint/widths.txt` (max widths 100 and 97);
  - `patches/COMMITS.tsv`, `patches/am-check.txt` (the tree reproduced from the patch; the commit is SSH-signed),
    `restore/restore-log.txt`, `tree/snapshot-pre.txt`, `restore/snapshot-post.txt` (the olean tree restored,
    SHA-256 `457ba704…` before and after), `PROVENANCE.txt`, `pr-body.md`.

Also: `pr.diff.txt` (2 paths, 167/0), `source-head.json` (hashes, line counts and over-width counts of the 2 files) and
`sources.zip` (the import closure at the head of both changed modules, 308 files). The consumer
`Cryptography/Randomness/Derandomization.lean` is not in that closure; it is in the bundle.

## Findings delivery

Return `gate28-derand-host-findings.md` as a Markdown file in this chat. If you have several evidence files, return a
ZIP. The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

**Severities**
- **blocker:** a false or unusable contract, or a scope violation (a frozen file changed).
- **major:** a missing or wrong hypothesis, a contract too weak for Theorem 180.1 or not provable on any reasonable
  route, a misplaced host under policy §1, a forbidden read, a duplicate public result, or necessary evidence that
  cannot be verified.
- **minor:** documentation or API defects, including an inaccurate formula docstring, route or proof sketch.
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

## ===== briefs/pass-shelat-ch5-8/maintainer/stmt-derand-2026-11-15/pr-body.md =====

# Statement: the seed-majority enumeration host (derand, PS10 Thm 180.1)

Draft maintainer statement PR, by Seyoon's ruling of 2026-11-14: the contract of the deterministic
counting/majority enumeration host that `bpp_subset_dtime_subexp` ([PS10, §8.2, Theorem 180.1]) needs is
stated first, as `sorry`, with its own gate. `derand` is dispatched only after that gate.

Branch `stmt/pass-shelat-derand-host` (local, not pushed), head `8972fb4ef15fa3d4e3df37d6aa8674408835593d`,
tree `ba544f9ca0d80ff12644128a2cc32a94d6b5f709`, on base `013119f006af40d03b88b0fc2d9b453cf0a9b348`
(`origin/cryptography/pass-shelat-ch2-4` after fetching, 2026-11-14).

## Changes

- **New:** `TCSlib/Complexity/Randomized/SeedMajority.lean` (163 lines).
  - `Complexity.seedMajority_mem_DTIME`: the host's contract. Stated; the only `sorry`.
  - `Randomized.half_lt_randProb_iff`: majority as a probability. Proved.
  - Module docstring: the formal reading, the consumers, the design, and the route for the fill.
- **Facade:** `TCSlib/Complexity/Randomized.lean` imports the module and lists it under `## Contents`.

## The statement

```lean
open Classical in
theorem seedMajority_mem_DTIME {V : Language Bool} (hV : V ∈ P) (w : ℕ → ℕ)
    (hw : PolyTimeComputable fun x => List.replicate (w x.length) true) :
    ∃ e : ℕ,
      {x : List Bool | 2 ^ w x.length <
          2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
            pairEncode x (List.ofFn u) ∈ V).card} ∈
        DTIME fun n => 2 ^ w n * (n + 1) ^ e := by
  sorry

theorem half_lt_randProb_iff (m : ℕ) (A : List Bool → Prop) [DecidablePred A] :
    1 / 2 < randProb m A ↔
      2 ^ m < 2 * (univ.filter fun r : Fin m → Bool => A (List.ofFn r)).card
```

## Design

- **The machine is existential.** The contract is a class membership in `DTIME`. That one
  membership carries both halves:
  - *correctness:* some machine decides exactly the strict-majority language;
  - *time:* it runs within `c · 2^{w(n)} · (n+1)^e`.

  Consumers read it only through published readers: `DTIME.mono`, `Randomized.DTIME_const_mul_subset`
  and `half_lt_randProb_iff`. No new `def` is introduced, so no sorried definition and no reader
  obligation arise (Rule 10).
- **Generality is what derand consumes, kept generic in what consumers vary.**
  - *The test* is any `V ∈ P` on `pairEncode x u`, so it depends on the input as well as the seed.
    `pairEncode` is the convention of `Randomized.polyTimeModel`, so derand's test is a `P`-preimage
    of its verifier's language.
  - *The width* is any `w` with a polynomial-time unary word. Derand uses the integer root `ℓ(n)`,
    piecewise with the true coin length `m(n)` below a threshold, which removes the need for a
    finite-table lemma.
  - *The count* is the `Finset` numerator of `randProb`, and *majority* is strict.
- **Placement.** The module goes in the shared Randomized layer of Complexity, not in derand's
  helper directory. Policy §1 puts hosts in the shared layer, there is a second consumer (`BPP ⊆ EXP`
  by coin enumeration, [AB09, p. 126]), and Complexity does not import Cryptography.
- **Nearest relatives, not reused.** `Complexity.exists_proj_decider` has an any-verdict, a fixed
  width `C(n+1)^c`, a test on `x ++ u`, and a private engine. The polynomial block-majority tests
  count over polynomially many blocks, not exponentially many seeds.

## Feasibility (the host fill)

1. **Pure layer, about 400–700 lines.**
   - The state is `⟨x, ⟨i, a⟩⟩`: the binary seed rank and the binary accept count.
   - Start at `⟨x, ⟨0, 0⟩⟩`. Each step adds `[⟨x, word_w(i)⟩ ∈ V]` to `a` and increments `i`.
     The run stops at `i = 2^{w}` with payload `[2^w < 2a]`.
   - Each piece is polynomial-time by `BinArith.polyTimeComputable_add`/`_lt`/`_beq`,
     `polyTimeComputable_ite`, `PolyTimeComputable.pairEncode`, `mem_P_iff_polyTimeComputable` and
     `hw`.
   - The state length is `O(n + w n)` by `PolyTimeComputable.output_length_le`.
2. **Machine, about 250–400 lines.** This is `Turing.FinTM.exists_loopFindTM` over
   `Complexity.IterateFind.hostTM`/`hostCtrl`/`hostRet`. The pieces are:
   - the modules `copyTM`/`copy_clean` and `Turing.ModuleHost.clean_install`/`clean_emit`;
   - `host_call`, `host_clean`, `host_dispatch`, `host_branch`, `host_halt`, `guard_add` and
     `request_budget`.

   It follows `Complexity.IterateFind.polyTimeComputable_find`'s proof, with the exponential fuel
   `Nat.bits (2^{w|x|})` (w zeros, then a one) taken from `hw`. The bound is
   `c (T n + 1)(2^{w n} + 2)` with `T` polynomial.

   `IterateFind`'s helpers `Inv`, `verdictWord`, `stepWord`, `outWord` and `final_bound` are private.
   The fill either re-derives them (about 100 lines, disclosed) or uses a harvested generic-fuel form;
   see the decisions below.
3. **Count, about 150–300 lines.**
   - The first stop index is `2^w` (`IterateFind.find?_range_and_lt` / `StateLoop.find?_range_eq_some`).
   - `a` equals the `Finset` count through the bijection `i ↦ word_w(i)` between `[0, 2^w)` and
     `Fin w → Bool` (Mathlib `finFunctionFinEquiv`, `Nat.testBit`).
4. **Normal form, about 80–150 lines.** Show `c (T n + 1)(2^{w n} + 2) ≤ b · 2^{w n} (n+1)^e`, then
   introduce the `DTIME` membership.
5. **Total: about 900–1,600 lines.** The brief estimated 1,500–3,000 for this item.
   - Every route lemma above prints only `propext`, `Classical.choice` and `Quot.sound`
     (`probes/RouteAxioms.log`).
   - The route uses none of the admitted `loopHostTM_*` and `timedCondTM_*` specs: `exists_loopFindTM`
     comes from the private, proved `loopHost_contracts`.

## Theorem 180.1 from the contract and the PRG hypothesis (paper proof)

**Setup.** Let `L ∈ BPP` have verifier `M` with `M x r = true ↔ ⟨x, r⟩ ∈ V₁ ∈ P` and `m(n) = a(n+1)^k`.
Fix `d ≥ 2` with `1/d < min(ε, 1)`, and let `ℓ(n)` be the least `t` with `n ≤ t^d`.

1. **Expand the generator.** From `∃ G, G.Secure`, obtain a secure `G'` with stretch at least
   `P(s) = a(s^d+1)^k + s + 1` (`prg_expand`, `PRG.Secure.truncateTo_easy`/`_negligible`) and an
   evaluator `F'` (`PRG.easy_iff`). Since `n ≤ ℓ(n)^d`, we have `m(n) ≤ P(ℓ(n))`.
2. **Bound the gap.** There is `n₀` such that `|Pr_u[M(x; F'(u)↾m)] − Pr_r[M(x; r)]| ≤ 1/12` for every
   `|x| ≥ n₀`.
   - Otherwise infinitely many input lengths are bad.
   - Each seed length `s` is `ℓ(n)` for at most `s^d + 1` values of `n`, so infinitely many seed
     lengths are bad.
   - Take one bad `x` per bad seed length as advice (`|x| ≤ s^d`), and let `D(1^s, y) = M(x; y↾m(|x|))`.
     It is a NUPPT by `verifier_toNUPPT` and `NUPPT.exists_withAdvice(On)`.
   - Then `prgAdv > 1/12` infinitely often (`randProb_eq_uprob`), which contradicts `PRG.secure_iff`.
3. **Define the test and the width.**
   - `w(n) = if n < n₀ then m(n) else ℓ(n)`. Its unary word is polynomial-time.
   - `V'' = {⟨x, u⟩ | if |x| < n₀ then ⟨x, u⟩ ∈ V₁ else ⟨x, F'(u)↾m(|x|)⟩ ∈ V₁}`. It is in `P` by
     `preimage_mem_P`, `inter`/`union`/`compl_mem_P`, `PolyTimeComputable.pairEncode` and
     `takePrefixByLen`.
4. **`L` is exactly the majority language of `(V'', w)`.**
   - Below `n₀` the coins are true, so the acceptance probability is at least `2/3` or at most `1/3`.
   - From `n₀` on, it is at least `2/3 − 1/12 = 7/12 > 1/2` or at most `1/3 + 1/12 = 5/12 < 1/2`.
   - `half_lt_randProb_iff` turns this into the count.
5. **Apply the contract.** There is `e` with `L ∈ DTIME (2^{w n} (n+1)^e)`.
6. **Absorb the bound.** For large `n`, `ℓ(n) ≤ n^{1/d} + 1`, so `2^{w n}(n+1)^e ≤ 2^{n^{1/d} + 1 + e log₂(n+1)}`.
   Since `1/d < ε`, this is at most `subexpBound ε n` from some `N` on.
   - The finitely many lengths below `max(N, n₀)` are absorbed into `c` (`subexpBound_pos`).
   - Hence `∀ n, 2^{w n}(n+1)^e ≤ c · subexpBound ε n`, and `DTIME.mono` followed by
     `Randomized.DTIME_const_mul_subset` closes the goal.
   - `probes/ConsumerProbe.lean` checks this step through readers only, with `DTIME`, `randProb`,
     `P`, `PolyTimeComputable` and `pairEncode` sealed.

## Checks (evidence `stmt-derand-evidence.zip`)

- **Build.** 63 modules are checked one at a time into `dl-oleans-2`, all rc 0 with 0 errors (both
  forms counted). They are:
  - the new module and its facade;
  - the 51 tip-vs-olean-base Cryptography modules and their downstream;
  - root `TCSlib` and `audits/pass-shelat/Checks`.

  The only `sorry` warning is `seedMajority_mem_DTIME` (`SeedMajority.lean:154`).
- **Axioms.** `seedMajority_mem_DTIME` has `sorryAx` (intended). `half_lt_randProb_iff` has the
  standard three.
- **Seals.**
  - Whole-file seal of the new module (`randProb`, `DTIME`, `P`, `PolyTimeComputable`, `pairEncode`):
    rc 0.
  - Paired control: passes unsealed, fails sealed exactly once.
  - Consumer probe: passes sealed apart from its control, which fails exactly once; passes unsealed.
- **Lint.**
  - `campaign_style_lint.py TCSlib/Cryptography --check8b`: 92 FAIL / 101 WARN at base and at head,
    identical line sets.
  - `TCSlib/Complexity --check8b`: 25 / 391 at both, identical line sets. Six pre-existing facade
    FAILs for `Randomized/Build/*` are unchanged.
  - The new file has no FAIL or WARN.
- **Width and size.** The changed files have at most 100 characters per line and 163 and 210 lines.
- **Tree.** `dl-oleans-2` is restored. Its snapshot SHA-256 is
  `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f` before and after, byte-identical.

## Decisions for Seyoon

1. **Placement and name.** `Complexity/Randomized/SeedMajority.lean`, with
   `Complexity.seedMajority_mem_DTIME`.
2. **Generality.**
   - The test is `V ∈ P`, not a decider with arbitrary time `Tv`. A generic-time form needs a clean
     module for a decider of arbitrary time.
   - Majority is strict, with no general threshold.
   - The test uses `pairEncode`, not `x ++ u`.
   - There is only the `DTIME` form, with no machine-level `DecidesInTime` contract.
3. **No head-envelope clause.** Policy §1 asks hosts for time and space clauses. This contract is
   decision-layer, as `exists_proj_decider` is.
4. **Registry row H17** (`machine-library-design.md` §14). It is not edited here; the draft is below.
5. **Fill route.** Either harvest a generic-fuel `computesFunInTime_find` into
   `Randomized/Build/IterateFind.lean` (preferred; `polyTimeComputable_find` would become its
   corollary), or have the fill re-derive the private `IterateFind` helpers, disclosed.
6. **Introducing `DTIME` membership.** There is no `mem_DTIME_iff` reader beside `DTIME`. Either
   approve the anonymous-constructor idiom used by `DTIME_const_mul_subset` and
   `mem_DTIME_of_decidesInTimeVia`, or add the reader, which rebuilds `DTIME`'s downstream.
7. **The derand brief.** Route step 4 and checkpoint 1 become a consumption of this contract. The
   finite table can fold into the width. Derand's closure gains `Randomized/SeedMajority` and
   `Randomized/QuasiPolyHierarchy`, so `order.txt` and `roots.txt` need regenerating.
8. **Sequencing.** Assign the gate number, and decide whether derand may run proved-modulo while the
   host fill runs.

## Draft registry row (for `machine-library-design.md` §14)

| H17 | **Seed-majority enumeration host:** `Complexity.seedMajority_mem_DTIME` in `TCSlib/Complexity/Randomized/SeedMajority.lean`. For a test `V ∈ P` on `pairEncode x u` and a width `w` with a polynomial-time unary word, the strict-majority language `{x | 2^{w|x|} < 2·#{u ∈ {0,1}^{w|x|} : ⟨x,u⟩ ∈ V}}` is in `DTIME(2^{w(n)}·(n+1)^e)` for some `e`; reader `Randomized.half_lt_randProb_iff`. Decision layer; no head-envelope clause. | **Statement only**, in this PR; gate to be assigned. Fill route: `exists_loopFindTM` over the clean-module host (H14) with exponential fuel. | `bpp_subset_dtime_subexp` (derand, [PS10, Thm 180.1]); prospectively `BPP ⊆ EXP` by coin enumeration [AB09, p. 126]. |

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA

## ===== briefs/pass-shelat-ch5-8/fills/derand/issued-r1/brief.md =====

# Claude fill · pseudorandom generators derandomize `BPP` in subexponential time (`bpp_subset_dtime_subexp`, Theorem 180.1)

**Issue base** `107f1e8c218733eac12d6b9bee6fece441271317` on `cryptography/pass-shelat-ch2-4` (the records tip after #303, #305, #306,
#308 and #309; records-only commits since `58a061c9`). **Unit** `derand`. **Worker** Claude (standing ruling, 2026-11-11). **Lean** 4.25.0 and the
Mathlib revision in that commit's `lake-manifest.json`.

Prove the admitted theorem `bpp_subset_dtime_subexp` of [PS10, §8.2, Theorem 180.1] in
`TCSlib/Cryptography/Randomness/Derandomization.lean`. The statement passed the prong D statement phase (ruling D-6: stated against `main`'s `InBPP` and `DTIME`) and Gate 06,
and is frozen. Its docstring holds the maintainer's proof sketch.

## Feasibility (maintainer's assessment)

**Not dispatchable as a pure fill yet.** The statement looks true, but step 4 needs a counting enumeration host that the library lacks, and the hosts-first rule requires its contract to be statement-gated in the shared layer first. The machine construction must also avoid the admitted `Build/Loop` (`loopHostTM_*`) and `Build/Wrappers` (`timedCondTM_*`) specs in `base-sorries.txt`.

**Estimated size:** 4,000–8,000 lines: the counting host 1,500–3,000 (cf. the enumerator behind `NP_subset_EXP`), the PRG step 1,000–2,000, majority and time analysis 1,000–2,000, the seed schedule and table 500–1,000. The plan's prong D estimate was 2–4k lines and called this theorem machine-level.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4`. Start a local branch `fill/derand` at the exact issue base, and
  record the base in `REPORT.md`. Keep the proof branch local.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/derand/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `patches/COMMITS.tsv`: one row per commit, giving its hash, the author's name, email and date, and the
    committer's name, email and date, so that `git am` at the base reproduces every hash. Before you push,
    check the reproduction in a scratch clone and say so in `REPORT.md`. The last batch's worker hashes
    could not be reproduced, because no committer metadata was delivered;
  - `src/`: the changed and new files;
  - `evidence/`, with an `evidence/SHA256SUMS` manifest (see *Evidence completeness*);
  - a top-level `SHA256SUMS` listing every delivered file under `inbox/fills/derand/` except itself. The
    delivered paths must equal the manifest's paths exactly, with nothing missing and nothing extra.
    Check this before each push.
- Commit as `fill derand: checkpoint N` and `fill derand: final`.
- Pull with rebase before pushing, push only your delivery path, and never force-push. Campaign changes land
  by a maintainer PR for Seyoon's approval.

## Base and parallel work

- **#307 (dl-crh) is not merged.** It changes `Candidates/DiscreteLog.lean`, the `Hashing.lean` facade and `Hashing/FromDiscreteLog*`. This unit edits none of them, and its closure contains none of them.
- The other fills of this batch (`prf-mac`, `learning`, `seq-zk`, `canonizer`, `sc-ot`, `sc-compose`) start from the same base.
  Each edits only its own owned file and helper directory.

## Target (frozen; quoted from the issue base)

```lean
theorem bpp_subset_dtime_subexp (hPRG : ∃ G : PRG, G.Secure) (ε : ℝ) (hε : 0 < ε) :
    {L | Randomized.InBPP Randomized.polyTimeModel L} ⊆ DTIME (subexpBound ε) := by
  sorry
```

It lives in namespace `TCSlib.Cryptography.Randomness`. There are no section variables. The theorem takes `hPRG : ∃ G : PRG, G.Secure`, `ε : ℝ` and `hε : 0 < ε`.

- **`BPP`** is `Randomized.InBPP Randomized.polyTimeModel` (`Complexity/Randomized/PolyTimeModel.lean`): a
  polynomial-time verifier with randomness `polyLen a k |x|` and error `1/3`.
- **`DTIME T`** (`Complexity/ClassP/DTIME.lean`, `DTIME.mono`): decided by a finite binary multi-tape machine within
  `c · T(n)` for some `c`.
- **`subexpBound ε n = ⌈2^{n^ε}⌉₊`** (`subexpBound_eq`, `subexpBound_pos`, owned).
- **PRGs** (`Pseudorandom/Generators/Asymptotic/Defs.lean`, `…/Stretch.lean`): `PRG.secure_iff`, `PRG.easy_iff`,
  `prg_expand`, `PRG.Secure.truncate`, `PRG.Secure.truncateTo_easy`, `PRG.Secure.truncateTo_negligible`.
- **The bridge** (`Randomness/BPPBridge.lean`): `polyLenExpr_eq`, `verifier_toNUPPT`, `randProb_eq_uprob`.

Read the module docstring's *formal reading* and the target's six-step sketch: step 4 states that the machine
construction is "the substantive remaining fill obligation, not supplied by the sketch".

## Published interfaces

| Interface | Provider |
|---|---|
| `subexpBound_eq`, `subexpBound_pos` | owned file |
| `polyLenExpr_eq`, `verifier_toNUPPT`, `randProb_eq_uprob` | `Randomness/BPPBridge.lean` |
| `PRG`, `PRG.secure_iff`, `PRG.easy_iff`, `prg_expand`, `PRG.Secure.truncate`, `truncateTo_easy`, `truncateTo_negligible` | `Pseudorandom/Generators/Asymptotic/{Defs,Stretch}.lean` |
| `Randomized.InBPP`, `polyTimeModel` and its readers | `Complexity/Randomized/*` |
| `DTIME`, `DTIME.mono`, `FinTM.DecidesInTime` | `Complexity/ClassP/DTIME.lean` |
| `exists_proj_decider` (existential enumeration, the nearest host), `counterLoopTM` and the `Build/` catalog (`machine-library-design.md` §14 is the host registry) | `Complexity/ClassNP/EXP.lean`, `Complexity/TuringMachine/Build/*` |
| `polyTimeComputable_blockMajorityTest` (majority over polynomially many blocks) | `Complexity/ClassNP/PolyTimeBlockMajority.lean` |
| `NUPPT.exists_withAdvice(On)` (advice: one bad input per seed length), `Negligible` readers | `Complexity/Randomized/Closure.lean`, `Foundations/Negligible.lean` |

## Proof route and checkpoints

1. **Checkpoint 1 · the counting enumerator host (scope request first).** Step 4 needs a deterministic machine that runs a decider on `x ++ u` for every seed `u` of width `w` and accepts iff more than half accept, within `b · 2^w · (T(n + w) + poly)`. No such host exists: `exists_proj_decider` is existential, its engine `enumMachine_contracts` is private, and the majority tests are polynomial-time over polynomially many blocks. Policy §1 (*Hosts come first*) forbids building it privately. Write its contract (statement and proof sketch, generic in the decider) and send it as a scope request to Seyoon before proving anything that depends on it. Send this checkpoint.
2. **Checkpoint 2 · the PRG step (sketch steps 1–2).** The integer seed schedule `ℓ(n)` (least `t` with `n ≤ t^d`), the envelope `P`, the expanded and truncated generator, and the contradiction: infinitely many bad input lengths give a non-uniform distinguisher at infinitely many seed lengths (advice: one bad input each, length at most `s^d`; `verifier_toNUPPT`, `randProb_eq_uprob`). Send this checkpoint.
3. **Checkpoint 3 · majority correctness (sketch step 3).** Eventually every input has gap at most `1/12`, so `M'` is correct with probability at least `7/12` and the majority over all seeds is correct. Send this checkpoint.
4. **Final · the machine and the time bound (sketch step 4).** The host applied to `M'` (with `G` run by its evaluator), the time `2^{ℓ(n)} · poly(n) ≤ c · 2^{n^ε}` eventually, and a finite table for the remaining lengths, giving `DTIME (subexpBound ε)`.

Check the edge cases: small `n` (the finite table); `ε ≥ 1`; `d` with `1/d < min(ε, 1)`; seed lengths shared by many input lengths; the expanded generator's output envelope at `s = ℓ(n)`; ties in the majority (the `1/12` margin excludes them).

If the sketch is wrong, or a target is false as stated, stop and escalate with the exact obligation: a
checkpoint with the counterexample or the missing fact. Do not weaken any statement.

## Scope and proof discipline

- **Owned file.** You own `TCSlib/Cryptography/Randomness/Derandomization.lean` (97 lines at the issue base):
  - replace the target's proof body and edit its sketch to describe the delivered proof;
  - update the module title (drop "(statement phase)" where present) and the `## Main results` status.
- **Helper modules.**
  - They are permitted under `TCSlib/Cryptography/Randomness/Derandomization/`. The owned file imports them precisely and gets a
    `## Contents` list.
  - **Facades.** After the facade-lint fix (#305), a new helper under `X/` is covered as long as `X.lean`
    imports it, so no parent facade needs an edit.
  - Helpers may import the machine library and the complexity classes already in the closure (for example `Complexity/ClassNP/EXP`, `Complexity/TuringMachine/Build/*`).
- **Size and width.** Every line has at most 100 characters (Python `len`), and every file at most 1000 lines.
  Check both with a short `python3 -I` script before each push and include its output in `evidence/`.
- **Frozen files.** Do not edit any other file.
  - `Games/Efficiency.lean` is at 982 lines. Do not add to it.
  - **Scope requests.** If the route needs a change to a frozen file (a reader beside a foreign definition, an
    import, a promotion), stop that line of work. Ask Seyoon in your session, giving the exact file, the diff
    and the reason, and go ahead only on his approval. Record the request and his answer verbatim under
    `evidence/scope-request/` and in `REPORT.md` § *Scope requests*. The Codex fills obtained their facade
    imports, and dl-crh its two `DiscreteLog` readers, this way. Seyoon prefers a route with no frozen-file edit
    where one exists.
  - A lemma that belongs in an existing file goes in your helper module, with a promotion request.
- **Parallel fills.** The seven fills `prf-mac`, `learning`, `derand`, `seq-zk`, `canonizer`, `sc-ot` and
  `sc-compose` are issued from the same base. Edit only your owned file and helper directory.
- **Duplication (binding).**
  - **Search first.** Before writing any lemma, search `TCSlib/` and Mathlib for its statement shape and key
    names. Reuse published lemmas by importing them.
  - **Private lemmas.** Never copy a private lemma silently. If you need one, re-derive it from published
    readers, keep its statement general, and disclose it.
  - **Disclose every overlap.** `REPORT.md` has a section **`## Overlap and reuse`**. For every new declaration
    that restates, specializes or re-proves existing material (public or private, TCSlib or Mathlib), give its
    nearest relative (`path:line`), the relation, and why it is not reused. List the searches you ran.
  - **Why.** Undisclosed duplication is a freeze violation, not debt. The majors that held Gates 23 and 24
    were undisclosed duplicates: G23-01, a private copy of `length_le_length_encodeLog`; G24-01,
    `inputWord_take`, which re-proves the public `take_ofFn_castLE`.
  - **Nearest relatives here:** `Complexity.NP_subset_EXP` and its enumerator `exists_proj_decider` (`ClassNP/EXP.lean`), `Randomized.mem_EXP_of_inBPP_polyTimeModel` (`Randomized/Inclusions.lean`, via Sipser–Gács), the block-majority tests (`ClassNP/PolyTimeBlock*.lean`) and `BPPAmplify`.
- **Statements.** Preserve the target statement, every other declaration, the statement prose and the global
  simp attributes.
- **Docstrings and sketches.** The last batch's landing edits were mostly LE-doc (cca2-ett: 94 formulas and
  15 sketches; dl-crh: 59 formulas; lamport: 188 formulas and 7 sketches) and LE-width. Do these yourself:
  - every new public declaration has a docstring that states its formula: the equation or inequality, with its
    arguments in the Lean order, and a `[PS10, …]` tag where it comes from the source;
  - every proof of 15 lines or more carries a `**Proof sketch.**` paragraph, and long proofs get step comments
    (policy §3);
  - a new public `def` lands with its `_eq`, `_iff` or `simps` readers (lint check 8), and a new public
    `abbrev` with an `_eq` or `_iff` lemma;
  - add no `@[simp]`.
- **Rule 10.**
  - Use only published readers for other files' definitions, including generated matchers and projections.
  - Your helper modules count as foreign to each other and to the owned file. The owned file's definitions
    are foreign to your helpers.
  - **Notation, never sealed:**
    - `PolyExpr.eval` (Q1);
    - reducible abbreviations (2026-10-26; for example `QueryImpl`, `OracleSpec.add`, `glNeed`);
    - **projection coercions:** a `CoeFun`/`Coe` instance whose body is a structure projection, such as
      `FinDist`'s `⟨FinDist.prob⟩` (Seyoon's ruling, 2026-11-14).

    The coe-variant seals are canonical. Run the strict variant as well, and attribute each difference.

## Checks and report

- **Bootstrap.**
  - Bootstrap from `order.txt` (203 modules) and the narrow `roots.txt` (80), following the addendum.
  - Check one module per `scripts/lean_check_tree.sh` call, with one Lean process per olean tree.
  - Never run `lake build` or an unfiltered cache get. Run Python as `python3 -I`.
  - Insert helper modules before their consumers.
- **Sweep.**
  - Recheck the owned module, then sweep the supplied order with 0 errors.
  - Compare the `sorry` warnings with `base-sorries.txt` (20 declarations in 10 modules). The only change
    must be the removal of `bpp_subset_dtime_subexp`.
- **Axioms.**
  - Print the axioms of `bpp_subset_dtime_subexp`. Expect only `propext`, `Classical.choice` and `Quot.sound`.
  - Print them for every stored constant of the changed and new files.
- **Rule 10 evidence.**
  - Run whole-file seals A and B of every changed or new file over its full TCSlib import closure, at base and
    final.
  - Run both the **strict** and the **coe** variant (projection coercions sealed, or treated as notation).
    Report every failing declaration in each.
  - Add paired controls that pass unsealed and fail sealed, each sealed negative failing exactly once.
  - Run the explicit-unfold scan.
  - Report the seals with `PolyExpr.eval` both excluded as notation and sealed.
  - **Error counts (G26-N1).** Your runner must count both diagnostic forms, `error:` and `error(…)`, for
    example with `^\S+\.lean:\d+:\d+: error[:(]`. Keep every raw log.
- **Lint.**
  - Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b` at base and at final.
  - The baseline at the issue base is **92 FAIL / 101 WARN** (after #305).
  - Diff the line sets, not only the counts. There must be no new FAIL line, and no new WARN line except one you
    disclose and justify.
- **Report.** `REPORT.md` gives:
  - the base and the status of each target;
  - the changed files and the sketch edits;
  - the new declarations;
  - **Overlap and reuse**;
  - **Scope requests** (none, or each with Seyoon's answer);
  - the promotion and reader requests;
  - the evidence, with its manifest.

### Evidence completeness

Gate 20 held a delivery for omitted raw evidence (G20-01).
- Every file that `evidence/SHA256SUMS` names must be delivered. That includes:
  - seal and control sources, manifests and request records;
  - every raw log and `results.jsonl`;
  - the probe sources and the tools used.
- If the evidence is too large for one commit, deliver it in several commits, or as numbered ZIP parts, each part
  with an entry list. Do not leave anything out for size.
- Check before delivery that the delivered paths are exactly the manifest's.

The maintainer checks `TCSlib` and `audits/pass-shelat/Checks` on the full-library tree at landing.

**Ready to dispatch**

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

## ===== TCSlib/Complexity/Randomized/SeedMajority.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.ClassP.P
import TCSlib.Complexity.ClassNP.PolyTime
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.Randomized.Classes

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deterministic majority over all seeds (statement phase)

The counting enumeration host: a deterministic machine that, on input `x`, runs a
polynomial-time test on `⟨x, u⟩` for **every** seed `u ∈ {0,1}^{w(|x|)}`, counts the accepting
seeds, and accepts iff more than half of them accept, in time `2^{w(n)} · poly(n)`. It is the
enumeration behind `BPP ⊆ EXP` [AB09, §7.1, p. 126] (run the machine on every random string
and count the accepting ones) and step 4 of the proof of [PS10, §8.2, Theorem 180.1] (run the
derandomized verifier on every seed of the generator and take the majority). It is a *host* in
the sense of `policy.md` §1 (*Hosts come first*): an odometer over all seeds, generic in the
leaf test `V` and in the width `w`. Its contract is stated here, ahead of its consumers, by
Seyoon's ruling of 2026-11-14; the proof is a separate fill.

**The formal reading.**
- **The test** is a language `V ∈ P` read on `Turing.pairEncode x u`, the library's two-argument
  convention (`Randomized.polyTimeModel`'s verifiers are read the same way), so that the test may
  depend on the input `x` as well as on the seed `u`.
- **The width** `w : ℕ → ℕ` depends on the input length only, and its unary word
  `x ↦ 1^{w(|x|)}` is polynomial-time computable. This makes `w` computable by the machine and
  bounds it polynomially (`Complexity.PolyTimeComputable.output_length_le`); it is otherwise
  arbitrary, so a consumer may use a non-polynomial schedule such as an integer root, or a
  piecewise one.
- **The count** is `#{u : Fin (w |x|) → Bool | ⟨x, u⟩ ∈ V}`, the numerator of
  `Randomized.randProb` (`Randomized.half_lt_randProb_iff` converts), and **majority** is the
  strict `2^{w(|x|)} < 2 · count`, so ties reject.
- **The time** is the class `DTIME (n ↦ 2^{w(n)} · (n+1)^e)` for some degree `e`: the machine
  is left existential and is read only through `DTIME`'s published readers (`DTIME.mono`,
  `Randomized.DTIME_const_mul_subset`). Membership in `DTIME` carries both halves of the
  contract: correctness (the machine decides exactly the majority language) and the time bound.

## Main results

* `Complexity.seedMajority_mem_DTIME` — the host's contract (stated; a `sorry` under the route
  below). [AB09, §7.1, p. 126]; [PS10, Theorem 180.1, step 4 of the proof]
* `Randomized.half_lt_randProb_iff` — majority as a probability:
  `1/2 < randProb m A ↔ 2^m < 2 · #{r | A r}` (proved).

## Consumers

* `TCSlib.Cryptography.Randomness.bpp_subset_dtime_subexp` ([PS10, Theorem 180.1]), with
  `V = {⟨x, u⟩ | M(x; G(u)↾m(|x|))}` and the seed schedule `w(n) = ℓ(n)` (the least `t` with
  `n ≤ t^d`); the true coins `w(n) = m(n)` below a threshold length replace the finite table.
* Prospectively, `BPP ⊆ EXP` by coin enumeration [AB09, p. 126] (`w = polyLen a k`), which
  `Randomized.mem_EXP_of_inBPP_polyTimeModel` currently obtains through Sipser–Gács.

## Design

* The nearest relative is the existential projection decider `Complexity.exists_proj_decider`
  (`ClassNP/EXP.lean`): the same odometer with an *any* verdict, a fixed width `C(n+1)^c` and
  the test on `x ++ u`. Its engine `enumMachine_contracts` and the `enumCont_*` body are
  private, it does not count, and its width is not a parameter, so it is not reused.
* The polynomial block-majority tests (`Complexity.polyTimeComputable_blockMajorityTest`) count
  over polynomially many blocks; this host counts over exponentially many seeds.
* The test is polynomial-time (`V ∈ P`), not a decider of arbitrary time `Tv` as in
  `exists_proj_decider`: both consumers have polynomial tests, and the clean-module host below
  installs polynomial-time word functions only (`Turing.ModuleHost.clean_install`).
* No head-envelope (space) clause is exposed: the contract is stated at the decision layer, as
  `exists_proj_decider` is, because its consumers need only time.

## Route for the proof (the fill)

1. *State loop.* The state word is `⟨x, ⟨i, a⟩⟩`: the binary rank `i` of the current seed and
   the binary acceptance count `a`, from `⟨x, ⟨0, 0⟩⟩`. A step tests `⟨x, word_w(i)⟩ ∈ V`,
   where `word_w(i)` is the width-`w(|x|)` binary word of `i`, adds the verdict to `a` and
   increments `i`. The loop stops when `i = 2^{w(|x|)}` and outputs `[decide (2^w < 2a)]`.
   Every piece is a polynomial-time word function of the state (`Complexity.BinArith`'s
   `add`, `lt` and `beq`, zero padding, the unary width, and `V`'s decider through
   `Complexity.mem_P_iff_polyTimeComputable`).
2. *Machine.* The result-bearing loop combinator `Turing.FinTM.exists_loopFindTM` over the
   clean-module host (`Turing.ModuleHost`, with `Complexity.IterateFind.hostTM`, `hostCtrl`,
   `hostRet`, `copyTM` and their run lemmas), exactly as in
   `Complexity.IterateFind.polyTimeComputable_find`, but with the exponential fuel
   `R(n) = 2^{w(n)}`, written as `Nat.bits (2^{w(|x|)})`
   (`w(|x|)` zeros, then a one) from the unary width. The combinator's bound is
   `c (T(n) + 1)(R(n) + 2)`, with `T` polynomial because every state word has length
   `O(n + w(n))` and `w(n) ≤ C(n+1)^c`. The admitted `loopHostTM_*` and `timedCondTM_*` specs
   are not used: `exists_loopFindTM` is proved from the private `loopHost_contracts`.
3. *Count.* The first stopping round is `2^{w(|x|)}`; there `a` counts the ranks `i < 2^w`
   whose word is accepted, which is the `Finset` count above through the bijection
   `i ↦ word_w(i)` between `[0, 2^w)` and `{0,1}^w`.
4. *Normal form.* `c (T(n) + 1)(2^{w(n)} + 2) ≤ b · 2^{w(n)} · (n+1)^e`, and `b` is absorbed by
   `DTIME`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge University
  Press, 2009, §7.1, p. 126 (`BPP ⊆ EXP` by enumerating the random strings) and Claim 2.4 (the
  enumeration argument of `NP ⊆ EXP`).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.2, Theorem 180.1 (book p. 180).
-/

namespace Randomized

open Finset

/-- **Majority as a probability.** For an event `A` on `m`-bit strings, the uniform probability
of `A` exceeds `1/2` exactly when more than half of the `2^m` strings satisfy it:
`1/2 < randProb m A ↔ 2^m < 2 · #{r : Fin m → Bool | A (List.ofFn r)}`. This converts the
counting form of `Complexity.seedMajority_mem_DTIME` into the probabilistic form of
[AB09, Def 7.3] and [PS10, Theorem 180.1]. -/
theorem half_lt_randProb_iff (m : ℕ) (A : List Bool → Prop) [DecidablePred A] :
    1 / 2 < randProb m A ↔
      2 ^ m < 2 * (univ.filter fun r : Fin m → Bool => A (List.ofFn r)).card := by
  rw [randProb_eq, lt_div_iff₀ (by positivity), ← Nat.cast_lt (α := ℚ)]
  push_cast
  constructor <;> intro h <;> linarith

end Randomized

namespace Complexity

open Turing

open Classical in
/-- **Deterministic majority over all seeds** [AB09, §7.1, p. 126]; [PS10, §8.2,
Theorem 180.1, step 4 of the proof]: for a test `V ∈ P` on paired words and a width
`w : ℕ → ℕ` whose unary word `x ↦ 1^{w(|x|)}` is polynomial-time computable, some degree `e`
puts the strict-majority language in `DTIME (n ↦ 2^{w(n)} · (n+1)^e)`:
`∃ e, {x | 2^{w(|x|)} < 2 · #{u : Fin (w |x|) → Bool | pairEncode x (List.ofFn u) ∈ V}}
∈ DTIME (fun n => 2^{w(n)} · (n+1)^e)`.
Membership in `DTIME` is the whole contract: a machine decides exactly this language
(correctness) within `c · 2^{w(n)} · (n+1)^e` steps (time). Ties (`2 · count = 2^w`) reject.

**Deviation.** The source's machine runs the test on every seed and counts; here the test is a
`P`-language on `Turing.pairEncode x u` and the count is a `Finset` count over
`Fin (w |x|) → Bool`, the numerator of `Randomized.randProb` (`Randomized.half_lt_randProb_iff`).

**Proof sketch** (the route of the module docstring).
1. Run the state loop `⟨x, ⟨i, a⟩⟩ ↦ ⟨x, ⟨i + 1, a + [⟨x, word_w(i)⟩ ∈ V]⟩⟩` from
   `⟨x, ⟨0, 0⟩⟩`, stopping at `i = 2^{w(|x|)}` with the payload `[2^w < 2a]`; each piece is a
   polynomial-time word function of the state.
2. Build the machine with the loop combinator `Turing.FinTM.exists_loopFindTM` over the
   clean-module host, as in `Complexity.IterateFind.polyTimeComputable_find`, with the fuel
   `Nat.bits (2^{w(|x|)})`; it halts within `c (T(n) + 1)(2^{w(n)} + 2)` with `T` polynomial,
   since `w(n) ≤ C (n+1)^c` (`PolyTimeComputable.output_length_le`).
3. At the stopping round, `a` is the number of accepted ranks `i < 2^w`, which equals the
   `Finset` count through the bijection `i ↦ word_w(i)` onto `{0,1}^w`.
4. Bound `c (T(n) + 1)(2^{w(n)} + 2)` by `b · 2^{w(n)} · (n+1)^e` and absorb `b` into `DTIME`. -/
theorem seedMajority_mem_DTIME {V : Language Bool} (hV : V ∈ P) (w : ℕ → ℕ)
    (hw : PolyTimeComputable fun x => List.replicate (w x.length) true) :
    ∃ e : ℕ,
      {x : List Bool | 2 ^ w x.length <
          2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
            pairEncode x (List.ofFn u) ∈ V).card} ∈
        DTIME fun n => 2 ^ w n * (n + 1) ^ e := by
  sorry

end Complexity

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
import TCSlib.Complexity.Randomized.SeedMajority

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
- `Randomized.SeedMajority`: the counting enumeration host, deterministic majority over all
  seeds of a polynomial-time test in `DTIME(2^{w(n)} · poly)` ([AB09, §7.1, p. 126];
  [PS10, Theorem 180.1]; statement phase).

All entries, and the files they describe, cite the printed book's (2009) numbering.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
-/

## ===== TCSlib/Cryptography/Randomness/Derandomization.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Randomness.BPPBridge
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.Defs
import TCSlib.Complexity.ClassP.DTIME

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Derandomization from pseudorandom generators (statement phase)

[PS10, Theorem 180.1]: if pseudorandom generators exist, then `BPP ⊆ DTIME(2^{n^ε})` for every
constant `ε > 0`.

**The formal reading.**
- **`BPP`** is `main`'s `Randomized.InBPP Randomized.polyTimeModel` ([AB09, Def 7.3]): an
  efficient verifier with randomness `polyLen a k |x|` and two-sided error `1/3` (decision D-6).
  It is inhabited: `P ⊆ BPP` is `Randomized.inBPP_polyTimeModel_of_mem_P`.
- **`DTIME(t)`** is `main`'s `Complexity.DTIME`, deterministic multi-tape time `O(t(n))`, the
  source's reading ("bounded by `O(t(n))`").
- **The bound** `2^{n^ε}` is taken with a real exponent and rounded up (`subexpBound`), so that
  every real `ε > 0` is covered, as in the source. It is at least `1` at every length
  (`subexpBound_pos`), so `DTIME (subexpBound ε)` is not empty for a trivial reason (`DTIME` of a
  bound that vanishes somewhere is).
- **"PRGs exist"** is `∃ G : PRG, G.Secure`, the ch. 2–4 layer's [PS10, Definition 77.1], secure
  against non-uniform distinguishers. A PRG of any stretch `ℓ(n) > n` gives one with any polynomial
  stretch by the ch. 2–4 expansion theorems (`PRG.Secure.truncate`, `prg_expand`), which the proof
  needs with a computable integer-root seed schedule and a syntactic polynomial output
  envelope, as specified in the proof sketch below.

## Main definitions

* `Randomness.subexpBound`: `n ↦ ⌈2^{n^ε}⌉`.

## Main results

* `Randomness.subexpBound_pos`: the bound is positive.
* `Randomness.bpp_subset_dtime_subexp` (Thm 180.1, stated; a `sorry` under the source's sketch).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.2, Theorem 180.1 (book p. 180).
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge University
  Press, 2009, Definitions 1.12 and 7.3 (`main`'s `DTIME` and `BPP`).
-/

namespace TCSlib.Cryptography.Randomness

open Complexity TCSlib.Cryptography

/-- The subexponential time bound `n ↦ ⌈2^{n^ε}⌉` (real exponent, rounded up). -/
noncomputable def subexpBound (ε : ℝ) (n : ℕ) : ℕ := ⌈(2 : ℝ) ^ ((n : ℝ) ^ ε)⌉₊

/-- The subexponential bound is the natural ceiling of `2^{n^ε}` with real exponents:
`subexpBound ε n = ⌈2^{n^ε}⌉₊`. -/
theorem subexpBound_eq (ε : ℝ) (n : ℕ) :
    subexpBound ε n = ⌈(2 : ℝ) ^ ((n : ℝ) ^ ε)⌉₊ := rfl

/-- The subexponential bound is positive at every length. -/
theorem subexpBound_pos (ε : ℝ) (n : ℕ) : 0 < subexpBound ε n :=
  Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)

/-- **Theorem 180.1: pseudorandom generators derandomize `BPP` in subexponential time**
[PS10, Theorem 180.1]: if a secure PRG exists, then every language of `main`'s `BPP` is in
`DTIME(2^{n^ε})` for every `ε > 0`.

**Proof sketch** (the source's, with the steps it leaves implicit; route note S3c).
1. Let `L ∈ BPP` have verifier `M` and randomness `m(n) = a(n+1)^k`. Fix an integer `d ≥ 2`
   with `1/d < min(ε,1)`. Compute `ℓ(n)` as the least natural `t` with `n ≤ t^d`, using integer
   comparisons and powers. Then `n ≤ ℓ(n)^d` and `ℓ(n) ≤ n^{1/d}+1`. No computation of an
   arbitrary real exponent is required. Expand the PRG to the syntactic polynomial envelope
   `P(s) = a(s^d+1)^k+s+1`, which exceeds `s` and covers `m(n)` whenever `s = ℓ(n)`.
2. Let `M'(x; u) = M(x; G(u)↾m(|x|))`, with seed length `ℓ(|x|)`. If infinitely many lengths
   have an input with acceptance-probability gap `> 1/12`, choose one corresponding bad input
   at each bad seed length. Its advice length is at most `s^d`. The verifier bridge, composed
   with prefix truncation, is therefore a distinguisher polynomial in `s`; the probabilities
   agree through `randProb_eq_uprob`. Each seed length has only finitely many corresponding
   input lengths, so infinitely many bad input lengths give infinitely many bad seed lengths,
   contradicting PRG security. The fixed `1/12` threshold leaves an explicit majority margin.
3. Eventually every input has probability gap at most `1/12`. Since `M` is correct with
   probability at least `2/3`, `M'` is correct with probability at least `7/12 > 1/2`.
   The majority over all seeds is correct. A finite table handles the remaining input lengths.
4. Construct a deterministic multi-tape machine enumerating the seeds, running `G` and `M`,
   and counting, using the shared TM construction layer. For some constants `C,C'`, its time
   is at most `2^{ℓ(n)} · poly(n) ≤ 2^{n^{1/d}+1+C log₂(n+1)+C'}`. Since `1/d < ε`, this is
   eventually at most `2^{n^ε}`; a constant factor absorbs the finite exceptions. This machine
   construction is the substantive remaining fill obligation, not supplied by the sketch. -/
theorem bpp_subset_dtime_subexp (hPRG : ∃ G : PRG, G.Secure) (ε : ℝ) (hε : 0 < ε) :
    {L | Randomized.InBPP Randomized.polyTimeModel L} ⊆ DTIME (subexpBound ε) := by
  sorry

end TCSlib.Cryptography.Randomness

## ===== TCSlib/Complexity/ClassP/DTIME.lean =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Computability.Language
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deciding languages and the classes DTIME

Languages are sets of binary strings, `Mathlib`'s `Language Bool`. A bundled finite
machine over the binary alphabet (`Turing.FinTM Bool`, tape alphabet
`Option Bool = {0, 1, blank}`) *decides* a language `L` in time `T` if on every input `x`
it halts within `T |x|` steps with the single-symbol output `[true]` if `x ∈ L` and
`[false]` otherwise. `DTIME T` is the class of languages decided in time `c · T` for some
constant `c`. [AB09, §1.6, Definition 1.12]

## Design and deviations from [AB09]

* [AB09] fixes the four-symbol alphabet `{▷, □, 0, 1}` for the definition and remarks the
  choice is immaterial. Our machines use the three-symbol tape alphabet
  `Option Bool = {0, 1, blank}` over bidirectional tapes, which need no start symbol
  ([AB09, Claim 1.8] direction). The alphabet-reduction theorem ([AB09, Claim 1.5],
  phase 2) will show that machines over any finite alphabet are simulated by binary ones
  with a constant-factor slowdown — absorbed by the `∃ c` in `DTIME` — so defining
  `DTIME` over binary machines loses no generality.
* Acceptance is by output (`[true]`/`[false]`), not by accepting states: the vendored
  model has a single halting state and distinguishes outcomes by output, which [AB09]
  does via the output tape as well.
* **The output tape is append-only** (the transition emits at most one symbol per step,
  and emitted symbols cannot be erased), whereas [AB09, §1.2] designates a read-write
  work tape as the output tape — [AB09, p. 19] itself lists write-only output among the
  benign model variations. This bridge is **waived** (phase-2 audit, finding 3; see
  the plan's decision log): [AB09]'s read-write-output machine is not formalized in
  this development, so no simulation between the conventions is even statable; the
  compensating restriction is that no exact [AB09] step count is ever imported as a
  formal bound. The in-model buffer-and-flush technique lives in
  `TCSlib.Complexity.TuringMachine.Composition`.
* **Initialization differs from [AB09]**: there are no start-marker (`▷`) cells — the
  bidirectional tapes make them unnecessary — and the input head begins on the first
  input symbol (on the boundary blank for empty input), with all work tapes blank.
* The constant `c` ranges over all of `ℕ`; `c = 0` yields the bound `0`, within which no
  machine can halt (the initial state is not the halting state), so it contributes
  nothing — this matches [AB09]'s `c > 0` without carrying a positivity side condition.

## Main definitions

* `Turing.FinTM.DecidesInTime` — `M` decides `L` within time `T`. [AB09, §1.6 with
  Definition 1.3]
* `Complexity.DTIME` — the class of languages decidable in time `c · T`.
  [AB09, Definition 1.12]

## Main results

* `Complexity.DTIME.mono` — `DTIME` is monotone in the time bound.
* `Complexity.DTIME_eq_empty_of_exists_zero` — a time bound that vanishes at some
  length has an empty class (every machine needs at least one step to halt).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.6; Definitions 1.3, 1.12.)
-/

namespace Turing.FinTM

/-- The machine `M` decides the language `L` within time `T`: on every input `x` it halts
within `T |x|` steps with output `[true]` if `x ∈ L` and `[false]` otherwise.
[AB09, §1.6 with Definition 1.3] -/
def DecidesInTime (M : FinTM Bool) (L : Language Bool) (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool,
    M.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x] (T x.length)

end Turing.FinTM

namespace Complexity

open Turing

/-- The class of languages decidable in time `c · T` for some constant `c`: a language
`L` is in `DTIME T` iff some finite binary-alphabet multi-tape machine decides it within
`c · T n` steps on inputs of length `n`. [AB09, Definition 1.12] -/
def DTIME (T : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInTime L fun n => c * T n}

/-- `DTIME` is monotone in the time bound.

**Proof sketch.** A machine deciding `L` within `c · T₁ n` steps also halts (with the
same output) within `c · T₂ n ≥ c · T₁ n` steps, by `Turing.FinTM.ComputesInTime.mono`
(halting is absorbing). -/
theorem DTIME.mono {T₁ T₂ : ℕ → ℕ} (h : ∀ n, T₁ n ≤ T₂ n) : DTIME T₁ ⊆ DTIME T₂ := by
  rintro L ⟨c, M, hM⟩
  exact ⟨c, M, fun x => (hM x).mono (Nat.mul_le_mul (le_refl c) (h x.length))⟩

/-- If the time bound vanishes at even one input length, the class is empty: the
initial state is not the halting state, so no machine halts in `c · 0 = 0` steps on an
input of that length (e.g. `List.replicate n false`).

**Proof sketch.** Given `T n = 0` and a claimed decider, instantiate `DecidesInTime` at
the input `List.replicate n false`; the budget is `c * T n = 0`, contradicting
`Turing.FinTM.not_computesInTime_zero`. -/
theorem DTIME_eq_empty_of_exists_zero {T : ℕ → ℕ} (h : ∃ n, T n = 0) : DTIME T = ∅ := by
  obtain ⟨n, hn⟩ := h
  ext L
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨c, M, hM⟩
  have hx := hM (List.replicate n false)
  simp only [List.length_replicate] at hx
  rw [hn, Nat.mul_zero] at hx
  exact M.not_computesInTime_zero _ _ hx

end Complexity

## ===== TCSlib/Complexity/Randomized/QuasiPolyHierarchy.lean =====

/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import Mathlib.Data.Nat.Size
import TCSlib.Complexity.ClassP.BinaryArith.PrimeFind
import TCSlib.Complexity.ClassNP.Transducer
import TCSlib.Complexity.TimeHierarchy.Diagonal

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# P is a proper subset of DTIME(n^{log n})

[AB09, §7.5, p.135]: "(by the Time Hierarchy Theorem) `BPP` [`= P`] is a proper subset of,
say, `DTIME(n^{log n})`." We prove `P ⊊ DTIME(n^{log n})` with `log = Nat.log 2`, by the
time hierarchy theorem — its two halves `diagLang_mem_DTIME` and `diagLang_not_mem_DTIME`
of `Complexity.time_hierarchy` — at the time-constructible budget
`2^{(log n)² + 1} ≤ 2 n^{log n}`.

## Main definitions

* `Randomized.quasiPolyBudget` — `n ↦ 2^{(log n)² + 1}`.

## Main results

* `Randomized.timeConstructible_quasiPolyBudget` — it is time constructible.
* `Randomized.P_ssubset_DTIME_pow_log` — `P ⊊ DTIME(n^{log n})`.

## Divergences

* The book says "say, `DTIME(n^{log n})`"; we fix `log = Nat.log 2` (so `0^{log 0} = 1`).
* The repository's hierarchy theorem needs `(f + n + 1)² = o(g)` and a constructible `g`,
  so the separating budget is `2^{(log n)² + 1}`, not `n^{log n}` itself; its diagonal
  language lies in `DTIME(n^{log n})` by monotonicity.
* Constructibility goes through `PolyTimeComputable`: the budget word `0^{(log n)²+1} 1` is
  emitted by `Complexity.polyTimeComputable_emitIter`, and a polynomial bound is within a
  constant of the superpolynomial budget.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Turing Complexity Complexity.TimeHierarchy

/-- The separating budget `n ↦ 2^{(log n)² + 1}`. -/
def quasiPolyBudget (n : ℕ) : ℕ := 2 ^ (Nat.log 2 n ^ 2 + 1)

/-! ### Arithmetic of the budget -/

/-- `n` has `log n + 1` binary digits (none for `n = 0`). -/
private theorem length_bits_eq (n : ℕ) : n.bits.length = if n = 0 then 0 else Nat.log 2 n + 1 := by
  rw [Nat.size_eq_bits_len]
  split_ifs with hn
  · subst hn; simp
  · refine le_antisymm (Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by norm_num) n)) ?_
    exact Nat.succ_le_of_lt (Nat.lt_size.mpr (Nat.pow_log_le_self 2 hn))

/-- `n ≤ 2^{(log n)² + 1}`. -/
theorem le_quasiPolyBudget (n : ℕ) : n ≤ quasiPolyBudget n := by
  have h1 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
  have h2 : Nat.log 2 n ≤ Nat.log 2 n ^ 2 := by nlinarith
  exact h1.le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- `1 ≤ n^{log n}` for every `n` (`0^{log 0} = 1`). -/
private theorem one_le_pow_log (n : ℕ) : 1 ≤ n ^ Nat.log 2 n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Nat.one_le_pow _ _ hn

/-- `2^{(log n)²} ≤ n^{log n}`. -/
theorem two_pow_log_sq_le (n : ℕ) : 2 ^ (Nat.log 2 n ^ 2) ≤ n ^ Nat.log 2 n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [sq, pow_mul]
    exact Nat.pow_le_pow_left (Nat.pow_log_le_self 2 hn.ne') _

/-- `2^{(log n)² + 1} + 1 ≤ 3 n^{log n}`. -/
theorem quasiPolyBudget_add_one_le (n : ℕ) :
    quasiPolyBudget n + 1 ≤ 3 * n ^ Nat.log 2 n := by
  have := two_pow_log_sq_le n
  have := one_le_pow_log n
  unfold quasiPolyBudget
  rw [pow_succ]
  omega

/-- A polynomial is within a constant of the budget: `(n+1)^c ≤ 2^{c(c+1)} 2^{(log n)²}`.

**Proof sketch.** `n + 1 ≤ 2^{m+1}` with `m = log n`, and `(m+1)c ≤ c(c+1) + m²` (split on
`m ≤ c`). -/
theorem succ_pow_le_quasiPoly (n c : ℕ) :
    (n + 1) ^ c ≤ 2 ^ (c * (c + 1)) * 2 ^ (Nat.log 2 n ^ 2) := by
  set m := Nat.log 2 n
  have h1 : n + 1 ≤ 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hexp : (m + 1) * c ≤ c * (c + 1) + m ^ 2 := by
    rcases le_or_gt m c with h | h
    · nlinarith
    · nlinarith
  calc (n + 1) ^ c ≤ (2 ^ (m + 1)) ^ c := Nat.pow_le_pow_left h1 c
    _ = 2 ^ ((m + 1) * c) := (pow_mul _ _ _).symm
    _ ≤ 2 ^ (c * (c + 1) + m ^ 2) := Nat.pow_le_pow_right (by norm_num) hexp
    _ = 2 ^ (c * (c + 1)) * 2 ^ (m ^ 2) := pow_add _ _ _

/-- On `n = 2^m` the budget beats `A (nᵏ + 1 + n + 1)²` once `m ≥ A + 2k + 6`.

**Proof sketch.** `nᵏ + n + 2 ≤ 2^{m(k+1)+2}` and `A < 2^A`, so the left side is below
`2^{A + 2m(k+1) + 4} ≤ 2^{m²}`. -/
theorem poly_sq_le_quasiPolyBudget (k A m : ℕ) (hm : A + 2 * k + 6 ≤ m) :
    A * ((2 ^ m) ^ k + 1 + 2 ^ m + 1) ^ 2 ≤ quasiPolyBudget (2 ^ m) := by
  unfold quasiPolyBudget
  rw [Nat.log_pow (by norm_num)]
  have hA : A < 2 ^ A := Nat.lt_two_pow_self
  have hk : (2 ^ m) ^ k ≤ 2 ^ (m * (k + 1)) := by
    rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hm1 : 2 ^ m ≤ 2 ^ (m * (k + 1)) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hone : 1 ≤ 2 ^ (m * (k + 1)) := Nat.one_le_two_pow
  have hsum : (2 ^ m) ^ k + 1 + 2 ^ m + 1 ≤ 2 ^ (m * (k + 1) + 2) := by
    rw [pow_add]; omega
  have hexp : A + (m * (k + 1) + 2) * 2 ≤ m ^ 2 + 1 := by nlinarith
  calc A * ((2 ^ m) ^ k + 1 + 2 ^ m + 1) ^ 2
      ≤ 2 ^ A * (2 ^ (m * (k + 1) + 2)) ^ 2 :=
        Nat.mul_le_mul hA.le (Nat.pow_le_pow_left hsum 2)
    _ = 2 ^ (A + (m * (k + 1) + 2) * 2) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ (m ^ 2 + 1) := Nat.pow_le_pow_right (by norm_num) hexp

/-! ### Constructing the budget -/

/-- Rewrite every symbol as `1` (a one-state transducer). -/
private def allTrue : List Bool → List Bool :=
  transduce (fun (_ : Unit) _ => ()) (fun _ _ => some true) ()

/-- Output one `0` per symbol after the first `0` (state: a `0` has been seen). -/
private def zerosAfterZero : List Bool → List Bool :=
  transduce (fun q b => q || !b) (fun q _ => if q then some false else none) false

/-- `allTrue l = 1^{|l|}`. -/
private theorem allTrue_eq (l : List Bool) : allTrue l = List.replicate l.length true := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [allTrue] at ih ⊢
    simp [transduce, ih, List.replicate_succ]

/-- After a `0` has been seen, every symbol emits `0`. -/
private theorem transduce_seen (l : List Bool) :
    transduce (fun q b => q || !b) (fun q _ => if q then some false else none) true l =
      List.replicate l.length false := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [transduce, ih, List.replicate_succ]

/-- `zerosAfterZero (1^j 0 l) = 0^{|l|}`. -/
private theorem zerosAfterZero_ones_zero (j : ℕ) (l : List Bool) :
    zerosAfterZero (List.replicate j true ++ false :: l) = List.replicate l.length false := by
  induction j with
  | zero => simp [zerosAfterZero, transduce, transduce_seen]
  | succ j ih => simpa [zerosAfterZero, transduce, List.replicate_succ] using ih

/-- `zerosAfterZero (1^j) = []`. -/
private theorem zerosAfterZero_ones (j : ℕ) : zerosAfterZero (List.replicate j true) = [] := by
  induction j with
  | zero => rfl
  | succ j ih => simpa [zerosAfterZero, transduce, List.replicate_succ] using ih

/-- On `w = 1^{m-1} 0 1^m`, the chunk of round `i` is `0^m` for `i < m` and empty after. -/
private theorem zerosAfterZero_drop (m i : ℕ) :
    zerosAfterZero ((List.replicate (m - 1) true ++ false :: List.replicate m true).drop i) =
      if i < m then List.replicate m false else [] := by
  split_ifs with hi
  · rw [List.drop_append_of_le_length (by simp; omega), List.drop_replicate,
      zerosAfterZero_ones_zero, List.length_replicate]
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · rcases i with _ | i
      · rfl
      · simp [zerosAfterZero, transduce]
    · have hlen : (List.replicate (m - 1) true ++ [false]).length = m := by simp; omega
      rw [show List.replicate (m - 1) true ++ false :: List.replicate m true =
          (List.replicate (m - 1) true ++ [false]) ++ List.replicate m true by simp,
        List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, hlen,
        List.drop_replicate, zerosAfterZero_ones]

/-- Rounds `0, …, R-1` of chunks `0^m` (for `i < m`) emit `0^{min(R,m)·m}`. -/
private theorem flatMap_range_ite (m R : ℕ) :
    (List.range R).flatMap (fun i => if i < m then List.replicate m false else []) =
      List.replicate (min R m * m) false := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [List.range_succ, List.flatMap_append, ih, List.flatMap_singleton]
    by_cases h : R < m
    · rw [if_pos h, ← List.replicate_add, Nat.min_eq_left h.le,
        Nat.min_eq_left (Nat.succ_le_of_lt h), Nat.succ_mul]
    · rw [if_neg h, List.append_nil, Nat.min_eq_right (not_lt.mp h),
        Nat.min_eq_right (by omega : m ≤ R + 1)]

/-- The loop's start word `1^{m-1} 0 1^m` with `m = log |x|`, built from `bits |x|`. -/
private def budgetSeed (x : List Bool) : List Bool :=
  allTrue ((x.length.bits).drop 2) ++ false :: allTrue ((x.length.bits).drop 1)

/-- `budgetSeed x = 1^{m-1} 0 1^m` for `m = log |x|`. -/
private theorem budgetSeed_eq (x : List Bool) : budgetSeed x =
    List.replicate (Nat.log 2 x.length - 1) true ++ false ::
      List.replicate (Nat.log 2 x.length) true := by
  have h := length_bits_eq x.length
  unfold budgetSeed
  rw [allTrue_eq, allTrue_eq, List.length_drop, List.length_drop, h]
  split_ifs with h0
  · simp [h0]
  · congr 2

/-- The budget word is the seed's emission loop followed by `01`. -/
private theorem bits_quasiPolyBudget (x : List Bool) :
    (quasiPolyBudget x.length).bits =
      (List.range (1 * ((budgetSeed x).length + 1) ^ 1 + 1)).flatMap
        (fun i => zerosAfterZero ((fun w : List Bool => w.drop 1)^[i] (budgetSeed x))) ++
        [false, true] := by
  set m := Nat.log 2 x.length
  have hR : m ≤ 1 * ((budgetSeed x).length + 1) ^ 1 + 1 := by
    rw [budgetSeed_eq]; simp; omega
  simp only [BinArith.iterate_drop_one, budgetSeed_eq]
  rw [List.flatMap_congr (fun i _ => zerosAfterZero_drop m i), ← budgetSeed_eq,
    flatMap_range_ite, Nat.min_eq_right hR, quasiPolyBudget, bits_two_pow_eq_replicate]
  simp [m, List.replicate_succ', sq]

/-- The budget word `x ↦ ⌞2^{(log |x|)² + 1}⌟` is polynomial-time computable.

**Proof sketch.** Build the seed `1^{m-1} 0 1^m` (`m = log |x|`) from `bits |x|` by tails and
a one-state transducer; the emit loop over its tails prints `0^m` in each of the first `m`
rounds, i.e. `0^{m²}`; append `01`. -/
theorem polyTimeComputable_bits_quasiPolyBudget :
    PolyTimeComputable (fun x => (quasiPolyBudget x.length).bits) := by
  have hbits : PolyTimeComputable (fun x : List Bool => x.length.bits) := by
    convert polyTimeComputable_pairFstD.comp BinArith.polyTimeComputable_countLoop using 1
    funext x
    simp [BinArith.countLoop_eq]
  have hT : PolyTimeComputable allTrue := polyTimeComputable_transduce _ _ _
  have hseed : PolyTimeComputable budgetSeed := by
    convert (hT.comp (polyTimeComputable_tail.comp (polyTimeComputable_tail.comp hbits))).append
      ((polyTimeComputable_const [false]).append (hT.comp (polyTimeComputable_tail.comp hbits)))
      using 1
    funext x
    simp only [budgetSeed, Function.comp_apply, List.drop_drop, List.singleton_append]
  have hloop := polyTimeComputable_emitIter polyTimeComputable_tail
    (polyTimeComputable_transduce _ _ _ : PolyTimeComputable zerosAfterZero) 1 1 1 1
    (fun w i => by rw [BinArith.iterate_drop_one]; simp; omega)
  convert (hloop.comp hseed).append (polyTimeComputable_const [false, true]) using 1
  funext x
  rw [bits_quasiPolyBudget]
  rfl

/-- **`2^{(log n)² + 1}` is time constructible.**

**Proof sketch.** A machine computes the budget word within `C(n+1)^c` steps
(`polyTimeComputable_bits_quasiPolyBudget`), and `C(n+1)^c ≤ C 2^{c(c+1)} 2^{(log n)²}`
(`succ_pow_le_quasiPoly`); the budget is at least `n` (`le_quasiPolyBudget`). -/
theorem timeConstructible_quasiPolyBudget : TimeConstructible quasiPolyBudget := by
  obtain ⟨M, C, c, hM⟩ := polyTimeComputable_bits_quasiPolyBudget
  refine ⟨le_quasiPolyBudget, C * 2 ^ (c * (c + 1)) + 1, by omega, M, fun x => (hM x).mono ?_⟩
  have h := Nat.mul_le_mul_left C (succ_pow_le_quasiPoly x.length c)
  have hq : 2 ^ (Nat.log 2 x.length ^ 2) ≤ quasiPolyBudget x.length + 1 := by
    have := Nat.pow_le_pow_right (n := 2) (by norm_num) (Nat.le_succ (Nat.log 2 x.length ^ 2))
    unfold quasiPolyBudget
    omega
  calc C * (x.length + 1) ^ c ≤ C * 2 ^ (c * (c + 1)) * 2 ^ (Nat.log 2 x.length ^ 2) := by
        rw [Nat.mul_assoc]; exact h
    _ ≤ (C * 2 ^ (c * (c + 1)) + 1) * (quasiPolyBudget x.length + 1) :=
        Nat.mul_le_mul (Nat.le_succ _) hq

/-! ### The separation -/

/-- A constant factor in the time bound does not change `DTIME`. -/
theorem DTIME_const_mul_subset (C : ℕ) (T : ℕ → ℕ) : DTIME (fun n => C * T n) ⊆ DTIME T := by
  rintro L ⟨c, M, hM⟩
  exact ⟨c * C, M, fun x => (hM x).mono (le_of_eq (Nat.mul_assoc _ _ _).symm)⟩

/-- `nᵏ + 1 ≤ (2^{k²} + 2) n^{log n}`. -/
theorem pow_add_one_le_pow_log (k n : ℕ) :
    n ^ k + 1 ≤ (2 ^ (k * k) + 2) * n ^ Nat.log 2 n := by
  have h1 := one_le_pow_log n
  have hk : n ^ k ≤ 2 ^ (k * k) + n ^ Nat.log 2 n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rcases k with _ | k <;> simp
    by_cases hkl : k ≤ Nat.log 2 n
    · exact (Nat.pow_le_pow_right hn hkl).trans (Nat.le_add_left _ _)
    · have hlt : n < 2 ^ k :=
        (Nat.lt_pow_succ_log_self (by norm_num) n).trans_le
          (Nat.pow_le_pow_right (by norm_num) (by omega))
      calc n ^ k ≤ (2 ^ k) ^ k := Nat.pow_le_pow_left hlt.le k
        _ = 2 ^ (k * k) := (pow_mul _ _ _).symm
        _ ≤ _ := Nat.le_add_right _ _
  have h2 : 2 ^ (k * k) * 1 ≤ 2 ^ (k * k) * n ^ Nat.log 2 n := Nat.mul_le_mul_left _ h1
  rw [add_mul]
  omega

/-- **`P ⊊ DTIME(n^{log n})`** [AB09, §7.5, p.135, by Theorem 3.1].

**Proof sketch.** `P ⊆`: `nᵏ + 1 ≤ (2^{k²} + 2) n^{log n}`. Properness: the diagonal language
of the constructible budget `g = 2^{(log n)²+1}` lies in `DTIME(g + 1) ⊆ DTIME(n^{log n})`
(`g + 1 ≤ 3 n^{log n}`), but in no `DTIME(nᵏ + 1)`: at `n = 2^m` with `m` large,
`A (nᵏ + 1 + n + 1)² ≤ g(n)` (`poly_sq_le_quasiPolyBudget`, `diagLang_not_mem_DTIME`). -/
theorem P_ssubset_DTIME_pow_log : P ⊂ DTIME (fun n => n ^ Nat.log 2 n) := by
  refine ⟨fun L hL => ?_, fun h => ?_⟩
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hL
    exact DTIME_const_mul_subset (2 ^ (k * k) + 2) _
      (DTIME.mono (pow_add_one_le_pow_log k) hk)
  · have hmem : diagLang quasiPolyBudget ∈ DTIME (fun n => n ^ Nat.log 2 n) :=
      DTIME_const_mul_subset 3 _ (DTIME.mono quasiPolyBudget_add_one_le
        (diagLang_mem_DTIME timeConstructible_quasiPolyBudget))
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (h hmem)
    refine diagLang_not_mem_DTIME (T := fun n => n ^ k + 1) (fun A N => ?_) hk
    refine ⟨2 ^ max N (A + 2 * k + 6), ?_, poly_sq_le_quasiPolyBudget k A _ (le_max_right _ _)⟩
    exact (le_max_left _ _).trans Nat.lt_two_pow_self.le

/-- `P ≠ DTIME(n^{log n})`. -/
theorem P_ne_DTIME_pow_log : P ≠ DTIME (fun n => n ^ Nat.log 2 n) :=
  P_ssubset_DTIME_pow_log.ne

end Randomized

## ===== TCSlib/Complexity/Randomized/Build/IterateFind.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic.FinCases
import TCSlib.Complexity.TuringMachine.Build.Primitives
import TCSlib.Complexity.Randomized.Build.IterateFindHost
import TCSlib.Complexity.Randomized.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The machine behind the repetition lemma

The finite machine behind `Complexity.polyTimeComputable_iterateFind`
(`TCSlib.Complexity.Randomized.Repetition`, the load-bearing lemma of the Pass–shelat campaign,
foundation decision D11 of `PassShelatChapter2-4Plan.md`): iterate a polynomial-time step `g`
at most `R(|x|)` times on a polynomially bounded orbit and return the payload `out` of the first
orbit point accepted by `acc` (`[]` on exhaustion). Every theorem of [PS10, ch. 2–4] that
repeats an adversary — Algorithm 38.5's `2nm²p(n)` attempts with first success
[PS10, Theorem 35.1], the `n(2^k − 1)` calls of Goldreich–Levin [PS10, Theorem 87.3], the
truncated simulators [PS10, Algorithms 123.4 and 128.7] — reduces to this machine.

## Construction (DESIGN.md §2.6, the three panel repairs built in)

The machine is an instance of the result-bearing loop combinator
`Turing.FinTM.exists_loopFindTM` (`TCSlib.Complexity.TuringMachine.Build.Loop`).

1. *State word.* The loop state is the pair `⟨x, s⟩` (`Turing.pairEncode x s`) of the input
   and the current orbit point; the loop invariant `Inv` says the word *is* such a pair with
   `|s| ≤ P|x|`; the step is the length-guarded `Complexity.IterateFind.step`
   (`⟨x, g s⟩` if `|g s| ≤ P|x|`, else unchanged), under which the invariant is closed for
   every admissible word; on the orbit the guard never fires (the pure lemmas of
   `TCSlib.Complexity.Randomized.Repetition`).
2. *Modules.* Three clean-call modules over the state word, from
   `Turing.FinTM.exists_installCallTM`/`exists_emitCallTM` applied to FP functions: the
   **verdict** install `w ↦ ⟨[acc (snd w)], w⟩` (the verdict as the first cell of the installed
   word), the **step** install `w' ↦ step` on the pair carried by `w'`, and the **payload** emit
   `w' ↦ out (snd (snd w'))`; plus the startup module `x ↦ ⟨x, x⟩`
   (`Turing.FinTM.computesFunInTime_pairDup`) and a two-state copier that puts the native
   input on tape 0 first.
3. *Gluing.* Each module is converted into a first-halting source (a release flag stops it one
   silent step after its first positive exit), padded to the common tape count, and embedded
   into one finite host through the forwarding transformer `Turing.emitAction`; the host's own
   control has three fresh states — the loop **anchor** (never a module-internal state), a
   **branch** state reading the verdict cell of tape 0, and a **halt** state. Modules return
   to fixed host states: copier → startup install → anchor; verdict → branch; branch → payload
   emit (verdict `true`) or step install (verdict `false`); payload emit → halt; step → anchor.
4. *Budgets.* All requests are state words of length at most `Q n + 4` with
   `Q n = 2n + 2 + P n`; every module's polynomial budget on its argument is majorised by one
   common `A · (Q n + 5)^D`, which also pays for the fuel machine `x ↦ Nat.bits (R|x|)`
   (`Complexity.polyTimeComputable_unaryPoly R` composed with
   `Turing.FinTM.computesFunInTime_lengthBits`, so that the `find?` range is exactly
   `R|x| + 1`). The loop combinator returns a machine within `c (T n + 1)(R n + 2)`, which
   `PolyExpr.eval_le` puts in the normal form of `Complexity.PolyTimeComputable`.

The clean modules and the finite host (steps 2–3: release-flag stop, padding, forwarding host,
first-halt cutting) are the public clean-module host
`TCSlib.Complexity.TuringMachine.Build.ModuleHost` (host H14 of `machine-library-design.md` §14);
its instance for this machine (the copier, the control table, the return states) lives in
`TCSlib.Complexity.Randomized.Build.IterateFindHost`.
This file supplies the pure step, the FP functions of the modules, the budget arithmetic, and the
assembly through `Turing.FinTM.exists_loopFindTM`.

## Main definitions

* `Complexity.IterateFind.step` — the length-guarded step on the state word (definitionally
  `Complexity.guardedStep`).

## Main results

* `Complexity.IterateFind.polyTimeComputable_find` — the loop-level form of the repetition
  lemma: the first accepted orbit point's payload along the guarded orbit of `⟨x, x⟩` is
  polynomial-time computable.
* `Complexity.IterateFind.find?_congr_of_mem` — `List.find?` depends only on the predicate's
  values on the list (used to identify the guarded orbit with `g^[i] x`).
* `Complexity.IterateFind.find?_range_and_lt` — a search over `[0, L)` whose test also demands
  `i < N` is the search over `[0, N)`, for `N ≤ L`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 38.5 and Theorem 35.1; Theorem 87.3; Algorithms 123.4 and 128.7.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–1.3, time-bounded machines.)
-/

namespace Complexity.IterateFind

open Turing

/-! ### The guarded step on the state word and its FP pieces -/

/-- The length-guarded step on the state word `w = ⟨x, s⟩`: advance to `⟨x, g s⟩` if the new
orbit point fits the bound `P|x|`, else stay (DESIGN.md §2.6, step 1). This is definitionally
`Complexity.guardedStep g P x w`; it is restated here because this file is imported by the
file defining `guardedStep`. -/
def step (g : List Bool → List Bool) (P : PolyExpr) (x w : List Bool) : List Bool :=
  if (g (pairSndD w)).length ≤ P.eval x.length then pairEncode x (g (pairSndD w)) else w

/-- The guarded step: `step g P x w = ⟨x, g (snd w)⟩` if `|g (snd w)| ≤ P|x|`, and `w`
otherwise. -/
theorem step_eq (g : List Bool → List Bool) (P : PolyExpr) (x w : List Bool) :
    step g P x w =
      if (g (pairSndD w)).length ≤ P.eval x.length then pairEncode x (g (pairSndD w)) else w :=
  rfl

/-- The loop invariant used by the machine: the state word *is* a pair `⟨x, s⟩` with
`|s| ≤ P|x|` (stronger than the pure `Complexity.LoopInv`, which also admits malformed
words; the machine needs the well-formedness to bound the word's length). -/
private def Inv (P : PolyExpr) (x w : List Bool) : Prop :=
  ∃ s, w = pairEncode x s ∧ s.length ≤ P.eval x.length

/-- The initial word `⟨x, x⟩` is admissible when `|x| ≤ P|x|`. -/
private theorem inv_init (P : PolyExpr) (x : List Bool) (h0 : x.length ≤ P.eval x.length) :
    Inv P x (pairEncode x x) :=
  ⟨x, rfl, h0⟩

/-- The invariant is closed under the guarded step (the guard keeps the word unchanged when
the new point would be too long). -/
private theorem inv_step (g : List Bool → List Bool) (P : PolyExpr) (x w : List Bool)
    (h : Inv P x w) : Inv P x (step g P x w) := by
  obtain ⟨s, rfl, hs⟩ := h
  unfold step
  rw [pairSndD_pairEncode]
  split_ifs with hg
  · exact ⟨g s, rfl, hg⟩
  · exact ⟨s, rfl, hs⟩

/-- The length of an admissible state word is at most `2|x| + 2 + P|x|`. -/
private theorem inv_length (P : PolyExpr) (x w : List Bool) (h : Inv P x w) :
    w.length ≤ 2 * x.length + 2 + P.eval x.length := by
  obtain ⟨s, rfl, hs⟩ := h
  rw [length_pairEncode]
  omega

/-- The verdict word: `w ↦ ⟨[acc (snd w)], w⟩` (the verdict as the first cell, since
`pairEncode [b] w = [b, b, false, true] ++ w`). -/
private def verdictWord (acc : List Bool → Bool) (w : List Bool) : List Bool :=
  pairEncode [acc (pairSndD w)] w

/-- The step on a verdict word: strip the verdict, then take the guarded step on the pair
`⟨x, s⟩` carried by the word, with `x` recovered from the word itself. -/
private def stepWord (g : List Bool → List Bool) (P : PolyExpr) (w' : List Bool) : List Bool :=
  if (g (pairSndD (pairSndD w'))).length ≤ P.eval (pairFstD (pairSndD w')).length then
    pairEncode (pairFstD (pairSndD w')) (g (pairSndD (pairSndD w')))
  else pairSndD w'

/-- The payload of a verdict word: `out` of the orbit point `snd (snd w')`. -/
private def outWord (out : List Bool → List Bool) (w' : List Bool) : List Bool :=
  out (pairSndD (pairSndD w'))

/-- The first cell of a verdict word is the verdict. -/
private theorem verdictWord_head (acc : List Bool → Bool) (w : List Bool) :
    (verdictWord acc w)[0]? = some (acc (pairSndD w)) := by
  simp [verdictWord, pairEncode_eq]

/-- The length of a verdict word. -/
private theorem verdictWord_length (acc : List Bool → Bool) (w : List Bool) :
    (verdictWord acc w).length = w.length + 4 := by
  simp [verdictWord, length_pairEncode]
  omega

/-- On the verdict word of a pair `⟨x, s⟩`, `stepWord` is the guarded step. -/
private theorem stepWord_verdictWord (g : List Bool → List Bool) (P : PolyExpr)
    (acc : List Bool → Bool) (x s : List Bool) :
    stepWord g P (verdictWord acc (pairEncode x s)) = step g P x (pairEncode x s) := by
  simp [stepWord, verdictWord, step]

/-- On the verdict word of a pair, `outWord` is `out` of the orbit point. -/
private theorem outWord_verdictWord (out : List Bool → List Bool) (acc : List Bool → Bool)
    (x s : List Bool) : outWord out (verdictWord acc (pairEncode x s)) = out s := by
  simp [outWord, verdictWord]

/-- The verdict word is polynomial-time computable (`PolyTimeComputable.pairEncode` of the
test composed with the projection and the identity). -/
private theorem verdictWord_poly {acc : List Bool → Bool}
    (hacc : PolyTimeComputable fun s => [acc s]) : PolyTimeComputable (verdictWord acc) := by
  have h := (hacc.comp polyTimeComputable_pairSndD).pairEncode polyTimeComputable_id
  exact h

/-- The step on verdict words is polynomial-time computable.

**Proof sketch.** `Complexity.polyTimeComputable_ite`: the test
`|g (snd (snd w'))| ≤ P|fst (snd w')|` is `Complexity.polyTimeComputable_lenLe` on the pair
`⟨1^{P|fst (snd w')|}, g (snd (snd w'))⟩`, built with the unary evaluator
`Complexity.polyTimeComputable_unaryPoly P` and `PolyTimeComputable.pairEncode`; the `then`
branch is the pairing of the two projections (with `g`), the `else` branch the projection
`snd`; the Boolean test is identified with the propositional `if` by `decide_eq_true_eq`. -/
private theorem stepWord_poly {g : List Bool → List Bool} (hg : PolyTimeComputable g)
    (P : PolyExpr) : PolyTimeComputable (stepWord g P) := by
  have hs2 : PolyTimeComputable fun w' => pairSndD (pairSndD w') :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hf1 : PolyTimeComputable fun w' => pairFstD (pairSndD w') :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hgg : PolyTimeComputable fun w' => g (pairSndD (pairSndD w')) := hg.comp hs2
  have hun : PolyTimeComputable fun w' =>
      List.replicate (P.eval (pairFstD (pairSndD w')).length) true :=
    (polyTimeComputable_unaryPoly P).comp hf1
  have htest : PolyTimeComputable fun w' =>
      [decide ((g (pairSndD (pairSndD w'))).length ≤ P.eval (pairFstD (pairSndD w')).length)] := by
    have h := polyTimeComputable_lenLe.comp (hun.pairEncode hgg)
    convert h using 1
    funext w'
    simp
  have hthen : PolyTimeComputable fun w' =>
      pairEncode (pairFstD (pairSndD w')) (g (pairSndD (pairSndD w'))) := hf1.pairEncode hgg
  have h := polyTimeComputable_ite htest hthen polyTimeComputable_pairSndD
  convert h using 1
  funext w'
  simp [stepWord]

/-- The payload map on verdict words is polynomial-time computable. -/
private theorem outWord_poly {out : List Bool → List Bool} (hout : PolyTimeComputable out) :
    PolyTimeComputable (outWord out) :=
  hout.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The duplication `x ↦ ⟨x, x⟩` is polynomial-time computable. -/
private theorem dupWord_poly : PolyTimeComputable fun x => pairEncode x x :=
  polyTimeComputable_of_linear FinTM.computesFunInTime_pairDup

/-! ### Assembly -/

/-- `List.find?` depends only on the values of the predicate on the list's elements. -/
theorem find?_congr_of_mem {α : Type*} {p q : α → Bool} :
    ∀ l : List α, (∀ a ∈ l, p a = q a) → l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
    have ha : p a = q a := h a (List.mem_cons_self ..)
    by_cases hq : q a = true
    · rw [List.find?_cons_of_pos (by rw [ha]; exact hq), List.find?_cons_of_pos hq]
    · rw [List.find?_cons_of_neg (by rw [ha]; exact hq), List.find?_cons_of_neg hq]
      exact find?_congr_of_mem l (fun b hb => h b (List.mem_cons_of_mem a hb))

/-- **A bounded search is a search over a shorter range**: for `N ≤ L`, searching `[0, L)` for
the first `i` with `i < N` and `p i` is searching `[0, N)` for the first `i` with `p i`:
`(List.range L).find? (fun i => decide (i < N) && p i) = (List.range N).find? p`.

**Proof sketch.** Write `L = N + d` (`List.range_add`, `List.find?_append`). On `[0, N)` the guard
`i < N` holds, so the two predicates agree (`find?_congr_of_mem`). On the shifted tail `N + [0, d)`
it fails, so that search is `none` (`List.find?_eq_none`), and `o <|> none = o`. -/
theorem find?_range_and_lt (p : ℕ → Bool) {N L : ℕ} (hNL : N ≤ L) :
    (List.range L).find? (fun i => decide (i < N) && p i) = (List.range N).find? p := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNL
  rw [List.range_add, List.find?_append,
    find?_congr_of_mem _ (fun i hi => by rw [decide_eq_true (List.mem_range.1 hi), Bool.true_and])]
  have hnone : (List.map (fun x => N + x) (List.range d)).find?
      (fun i => decide (i < N) && p i) = none := by
    rw [List.find?_eq_none]
    intro x hx
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    rw [decide_eq_false (by omega), Bool.false_and]
    exact Bool.false_ne_true
  rw [hnone, Option.or_none]

/-- The final budget arithmetic: the loop combinator's bound `c (T n + 1)(R n + 2)` with
`T n = A (2n + 2 + P n + 5)^D` is in the normal form `C (n + 1)^e` once `P` and `R` are
majorised by `CP (n+1)^cP` and `CR (n+1)^cR`.

**Proof sketch.** `2n + 7 + P n ≤ (CP + 7)(n+1)^{cP+1}` (both `7(n+1)` and `CP (n+1)^{cP}`
are at most the corresponding multiples of `(n+1)^{cP+1}`); raise to the `D`-th power
(`Nat.pow_le_pow_left`, `Nat.mul_pow`, `Nat.pow_mul`), absorb the `+ 1` with
`1 ≤ (n+1)^{(cP+1)D}`, bound `R n + 2 ≤ (CR + 2)(n+1)^{cR}` likewise, and multiply
(`Nat.mul_le_mul`, `Nat.pow_add`). -/
private lemma final_bound (c A D CP cP CR cR n Pn Rn : ℕ)
    (hP : Pn ≤ CP * (n + 1) ^ cP) (hR : Rn ≤ CR * (n + 1) ^ cR) :
    c * (A * (2 * n + 2 + Pn + 5) ^ D + 1) * (Rn + 2) ≤
      c * (A * (CP + 7) ^ D + 1) * (CR + 2) * (n + 1) ^ ((cP + 1) * D + cR) := by
  have hpos : 0 < n + 1 := Nat.succ_pos n
  have h1 : 2 * n + 2 + Pn + 5 ≤ (CP + 7) * (n + 1) ^ (cP + 1) := by
    have ha : n + 1 ≤ (n + 1) ^ (cP + 1) := by
      simpa using Nat.pow_le_pow_right hpos (show 1 ≤ cP + 1 by omega)
    have hb : (n + 1) ^ cP ≤ (n + 1) ^ (cP + 1) := Nat.pow_le_pow_right hpos (by omega)
    have hc := Nat.mul_le_mul_left CP hb
    calc 2 * n + 2 + Pn + 5 ≤ 7 * (n + 1) + CP * (n + 1) ^ cP := by omega
      _ ≤ 7 * (n + 1) ^ (cP + 1) + CP * (n + 1) ^ (cP + 1) :=
          Nat.add_le_add (Nat.mul_le_mul_left 7 ha) hc
      _ = (CP + 7) * (n + 1) ^ (cP + 1) := by ring
  have h2 : (2 * n + 2 + Pn + 5) ^ D ≤ (CP + 7) ^ D * (n + 1) ^ ((cP + 1) * D) := by
    calc (2 * n + 2 + Pn + 5) ^ D ≤ ((CP + 7) * (n + 1) ^ (cP + 1)) ^ D :=
          Nat.pow_le_pow_left h1 D
      _ = (CP + 7) ^ D * (n + 1) ^ ((cP + 1) * D) := by rw [Nat.mul_pow, ← Nat.pow_mul]
  have hone : 1 ≤ (n + 1) ^ ((cP + 1) * D) := Nat.one_le_pow _ _ hpos
  have h3 : A * (2 * n + 2 + Pn + 5) ^ D + 1 ≤
      (A * (CP + 7) ^ D + 1) * (n + 1) ^ ((cP + 1) * D) := by
    calc A * (2 * n + 2 + Pn + 5) ^ D + 1
        ≤ A * ((CP + 7) ^ D * (n + 1) ^ ((cP + 1) * D)) + (n + 1) ^ ((cP + 1) * D) :=
          Nat.add_le_add (Nat.mul_le_mul_left A h2) hone
      _ = (A * (CP + 7) ^ D + 1) * (n + 1) ^ ((cP + 1) * D) := by ring
  have h4 : Rn + 2 ≤ (CR + 2) * (n + 1) ^ cR := by
    have hone' : 1 ≤ (n + 1) ^ cR := Nat.one_le_pow _ _ hpos
    calc Rn + 2 ≤ CR * (n + 1) ^ cR + 2 * (n + 1) ^ cR := by omega
      _ = (CR + 2) * (n + 1) ^ cR := by ring
  calc c * (A * (2 * n + 2 + Pn + 5) ^ D + 1) * (Rn + 2)
      ≤ c * ((A * (CP + 7) ^ D + 1) * (n + 1) ^ ((cP + 1) * D)) * ((CR + 2) * (n + 1) ^ cR) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left c h3) h4
    _ = c * (A * (CP + 7) ^ D + 1) * (CR + 2) * (n + 1) ^ ((cP + 1) * D + cR) := by
        rw [Nat.pow_add]; ring

/-- **The loop-level repetition lemma.** Let `g` be a polynomial-time step, `acc` a
polynomial-time test, `out` a polynomial-time payload map, and `R, P` syntactic polynomials
with `|g^[i] x| ≤ P|x|` for `i ≤ R|x|`. Then the function returning `out` of the orbit point
of the first index `i ≤ R|x|` at which `acc` accepts the second component of the `i`-fold
guarded step `Complexity.IterateFind.step g P x` from `⟨x, x⟩` (`[]` if none) is
polynomial-time computable. This is the machine behind
`Complexity.polyTimeComputable_iterateFind` [PS10, Algorithm 38.5, Theorem 35.1]; the pure
identification of the guarded orbit with `g^[i] x` is done there.

**Proof sketch.** Instance of `Turing.FinTM.exists_loopFindTM` for the host `hostTM` (the
clean-module host `Turing.ModuleHost.hostTM` with the control table `hostCtrl`) over the five
clean modules (the copier, and `Turing.ModuleHost.clean_install`/`clean_emit` of
`x ↦ ⟨x, x⟩`, `verdictWord acc`, `stepWord g P`, `outWord out`), with anchor `inl 0`,
invariant `Inv P`,
step `step g P`, acceptance `acc ∘ snd`, payload `out ∘ snd`, start word `⟨x, x⟩`. The fuel
machine computes `Nat.bits (R|x|)` (`polyTimeComputable_unaryPoly R` composed with
`computesFunInTime_lengthBits`). `hstart`: the copier (`copy_clean`, `ModuleHost.host_call`)
then the startup install (`ModuleHost.host_clean`) reach the anchor seam with `⟨x, x⟩` in
`2|x| + 2 + t_S` steps
with no earlier anchor visit. `hround`: from the anchor seam with an admissible word `⟨x, s⟩`,
the dispatch step, the verdict call, the branch step (`host_branch`), then either the payload
call and the halt step (`host_halt`) — state `none`, output `out s` — or the step call
returning to the anchor seam with `step g P x ⟨x, s⟩` (`stepWord_verdictWord`); the anchor
guard is `ModuleHost.guard_add` over the segments. All requests have length at most
`2|x| + 2 + P|x| + 4`, so every call fits the common budget `T n = A (2n + 2 + P n + 5)^D`
(`ModuleHost.request_budget`), and
`final_bound` puts the combinator's bound `c (T n + 1)(R n + 2)` in normal form. -/
theorem polyTimeComputable_find {g : List Bool → List Bool} (hg : PolyTimeComputable g)
    {acc : List Bool → Bool} (hacc : PolyTimeComputable fun s => [acc s])
    {out : List Bool → List Bool} (hout : PolyTimeComputable out)
    (R P : PolyExpr)
    (horbit : ∀ (x : List Bool) (i : ℕ), i ≤ R.eval x.length →
      (g^[i] x).length ≤ P.eval x.length) :
    PolyTimeComputable fun x =>
      match (List.range (R.eval x.length + 1)).find?
          (fun i => acc (pairSndD ((step g P x)^[i] (pairEncode x x)))) with
      | some i => out (pairSndD ((step g P x)^[i] (pairEncode x x)))
      | none => [] := by
  obtain ⟨S, aS, dS, hS⟩ := ModuleHost.clean_install dupWord_poly
  obtain ⟨V, aV, dV, hV⟩ := ModuleHost.clean_install (verdictWord_poly hacc)
  obtain ⟨I, aI, dI, hI⟩ := ModuleHost.clean_install (stepWord_poly hg P)
  obtain ⟨E, aE, dE, hE⟩ := ModuleHost.clean_emit (outWord_poly hout)
  have hbits : PolyTimeComputable fun x => Nat.bits (R.eval x.length) := by
    have h := (polyTimeComputable_of_linear FinTM.computesFunInTime_lengthBits).comp
      (polyTimeComputable_unaryPoly R)
    convert h using 1
    funext x
    simp
  obtain ⟨F, aF, dF, hF⟩ := (polyTimeComputable_iff _).1 hbits
  let M : Fin 5 → FinTM Bool := fun i => match i.val with
    | 0 => copyTM | 1 => S | 2 => V | 3 => I | _ => E
  let K := S.k + V.k + I.k + E.k
  have hk : ∀ i, (M i).k ≤ K + 1 := by
    intro i; fin_cases i <;> simp [M, K, copyTM_k] <;> omega
  let H := hostTM M K hk
  let anchor : H.State := .inl 0
  have hclean := ModuleHost.host_clean M (K + 1) hk (hostCtrl M K) (hostRet M)
    (ModuleHost.entry M 0)
  let D := dS + dV + dI + dE + dF + 1
  let A := aS + aV + aI + aE + aF + 5
  let pow (n : ℕ) := (2 * n + 2 + P.eval n + 5) ^ D
  let T (n : ℕ) := A * pow n
  have hpow (n : ℕ) : n + 1 ≤ pow n := by
    have h := Nat.pow_le_pow_right (show 0 < 2 * n + 2 + P.eval n + 5 by omega)
      (show 1 ≤ D by dsimp [D]; omega)
    simp only [Nat.pow_one] at h
    exact (by omega : n + 1 ≤ 2 * n + 2 + P.eval n + 5).trans h
  have hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ v < t, (H.tm.runFrom (H.tm.initCfg x) v).state ≠ some anchor) ∧
      H.tm.runFrom (H.tm.initCfg x) t = Cfg.ofWords anchor (stateWord H.k (pairEncode x x)) := by
    intro x
    obtain ⟨hcg, hce⟩ := copy_clean x
    obtain ⟨hcGuard, hcEnd⟩ := ModuleHost.host_call M (K + 1) hk (hostCtrl M K) (hostRet M)
      (ModuleHost.entry M 0) 0 (by simp [M, copyTM_k]) x [] x [] [] (0 : Fin 2)
      (2 * x.length + 2) hcg (by simpa using hce)
    have hi : H.tm.initCfg x = Cfg.ofWords (ModuleHost.entry M 0) (stateWord (K + 1) []) := by
      refine Cfg.ext ?_ rfl ?_ rfl rfl
      · exact congrArg some (ModuleHost.hostTM_tm_q₀ M (K + 1) hk (hostCtrl M K) (hostRet M)
          (ModuleHost.entry M 0))
      funext i z
      simp [MultiTapeTM.initCfg_eq, Cfg.init_state, Cfg.init_inputPos, Cfg.init_workTapes,
          Cfg.init_workTapePos, Cfg.init_output, Cfg.ofWords_def, stateWord_eq]
    change H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 0) (stateWord (K + 1) []))
      (2 * x.length + 2) = Cfg.ofWords (hostRet M 0) (stateWord (K + 1) x) at hcEnd
    rw [hostRet_zero] at hcEnd
    obtain ⟨ts, hspos, hst, hsGuard, hsEnd⟩ := hclean 1
      (fun x => pairEncode x x) (fun _ => []) (fun n => aS * (n + 1) ^ dS)
      (by simpa [M] using hS) x x []
    change H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 1) (stateWord (K + 1) x))
      ts = Cfg.ofWords (hostRet M 1) (stateWord (K + 1) (pairEncode x x)) at hsEnd
    rw [hostRet_one] at hsEnd
    have hsB := ModuleHost.request_budget aS dS D (2 * x.length + 2 + P.eval x.length + 5) x.length
      (by dsimp [D]; omega) (by omega)
    have hp := hpow x.length
    refine ⟨2 * x.length + 2 + ts, ?_, ?_, ?_⟩
    · dsimp only [T, A, pow]
      simp only [Nat.add_mul]
      dsimp only [pow] at hp
      omega
    · rw [hi]
      exact ModuleHost.guard_add H.tm anchor _ _ _ ts (fun v hv => hcGuard v hv 0) hcEnd
        (fun v hv => hsGuard v hv 0)
    · rw [hi, MultiTapeTM.runFrom_add, hcEnd, hsEnd]
      rfl
  have hround : ∀ x w : List Bool, Inv P x w → ∃ t, 0 < t ∧ t ≤ T x.length ∧
      (∀ t', 0 < t' → t' < t →
        (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t').state
          ≠ some anchor) ∧
      if acc (pairSndD w) then
        (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t).state = none ∧
        (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t).output =
          out (pairSndD w)
      else
        H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t =
          Cfg.ofWords anchor (stateWord H.k (step g P x w)) := by
    intro x w hw
    obtain ⟨s, rfl, hs⟩ := hw
    have hwlen : (pairEncode x s).length ≤ 2 * x.length + 2 + P.eval x.length := by
      rw [length_pairEncode]; omega
    have hw'len : (verdictWord acc (pairEncode x s)).length =
        (pairEncode x s).length + 4 := verdictWord_length acc _
    have hpow' := hpow x.length
    -- the dispatch, the verdict call, the branch
    have hdisp := host_dispatch M K hk x (pairEncode x s)
    obtain ⟨tv, hvpos, hvt, hvGuard, hvEnd⟩ := hclean 2 (verdictWord acc)
      (fun _ => []) (fun n => aV * (n + 1) ^ dV) (by simpa [M] using hV) x (pairEncode x s) []
    change H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 2) (stateWord (K + 1)
      (pairEncode x s))) tv = Cfg.ofWords (hostRet M 2) (stateWord (K + 1)
        (verdictWord acc (pairEncode x s))) at hvEnd
    rw [hostRet_two] at hvEnd
    have hbr := host_branch M K hk x (acc s) (verdictWord acc (pairEncode x s))
      (by rw [verdictWord_head, pairSndD_pairEncode])
    have hvB := ModuleHost.request_budget aV dV D (2 * x.length + 2 + P.eval x.length + 5)
      (pairEncode x s).length (by dsimp [D]; omega) (by omega)
    have hseg : H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 2)
        (stateWord (K + 1) (pairEncode x s))) (tv + 1) =
        Cfg.ofWords (ModuleHost.entry M (if acc s then 4 else 3))
          (stateWord (K + 1) (verdictWord acc (pairEncode x s))) := by
      rw [MultiTapeTM.runFrom_succ_eq_step', hvEnd, hbr]
    have hsegGuard : ∀ v < tv + 1, (H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 2)
        (stateWord (K + 1) (pairEncode x s))) v).state ≠ some anchor := by
      refine ModuleHost.guard_add H.tm anchor _ _ tv 1 (fun v hv => hvGuard v hv 0) hvEnd ?_
      intro v hv
      have hv0 : v = 0 := by omega
      subst hv0
      simp [Cfg.ofWords_def, anchor]
    by_cases hb : acc s = true
    · -- accepting round: the payload call, then the halt
      rw [if_pos hb] at hseg
      obtain ⟨te, hepos, het, heGuard, heEnd⟩ := hclean 4 id (outWord out)
        (fun n => aE * (n + 1) ^ dE) (by simpa [M] using hE) x
        (verdictWord acc (pairEncode x s)) []
      change H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 4) (stateWord (K + 1)
        (verdictWord acc (pairEncode x s)))) te = {Cfg.ofWords (hostRet M 4) (stateWord (K + 1)
          (verdictWord acc (pairEncode x s))) with
            output := [] ++ outWord out (verdictWord acc (pairEncode x s))} at heEnd
      rw [hostRet_four, List.nil_append, outWord_verdictWord] at heEnd
      have hhalt := host_halt M K hk x (verdictWord acc (pairEncode x s)) (out s)
      have heB := ModuleHost.request_budget aE dE D (2 * x.length + 2 + P.eval x.length + 5)
        (verdictWord acc (pairEncode x s)).length (by dsimp [D]; omega) (by omega)
      have hall : H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 2)
          (stateWord (K + 1) (pairEncode x s))) (tv + 1 + te + 1) =
          {Cfg.ofWords (input := x) (.inl 2 : ModuleHost.State (Fin 3) M) (stateWord (K + 1)
            (verdictWord acc (pairEncode x s))) with state := none, output := out s} := by
        rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add, hseg, heEnd, hhalt]
      have hallGuard : ∀ v < tv + 1 + te + 1, (H.tm.runFrom (Cfg.ofWords (input := x)
          (ModuleHost.entry M 2) (stateWord (K + 1) (pairEncode x s))) v).state ≠ some anchor := by
        refine ModuleHost.guard_add H.tm anchor _ {Cfg.ofWords (input := x)
          (.inl 2 : ModuleHost.State (Fin 3) M)
          (stateWord (K + 1) (verdictWord acc (pairEncode x s))) with output := out s}
          (tv + 1 + te) 1 ?_ ?_ ?_
        · exact ModuleHost.guard_add H.tm anchor _ _ (tv + 1) te hsegGuard hseg
            (fun v hv => heGuard v hv 0)
        · rw [MultiTapeTM.runFrom_add, hseg, heEnd]
        · intro v hv
          have hv0 : v = 0 := by omega
          subst hv0
          simp [Cfg.ofWords_def, anchor]
      refine ⟨tv + 1 + te + 1 + 1, by omega, ?_, ?_, ?_⟩
      · dsimp only [T, A, pow]
        simp only [Nat.add_mul]
        dsimp only [pow] at hpow'
        omega
      · intro v hv hvt
        have hvform : v = (v - 1) + 1 := by omega
        change (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
          (pairEncode x s))) v).state ≠ some anchor
        rw [hvform, MultiTapeTM.runFrom_succ_eq_step, hdisp]
        exact hallGuard (v - 1) (by omega)
      · rw [pairSndD_pairEncode, if_pos hb]
        change (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
            (pairEncode x s))) (tv + 1 + te + 1 + 1)).state = none ∧
          (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
            (pairEncode x s))) (tv + 1 + te + 1 + 1)).output = out s
        rw [MultiTapeTM.runFrom_succ_eq_step, hdisp, hall]
        exact ⟨rfl, rfl⟩
    · -- advancing round: the step call returns to the anchor
      rw [if_neg hb] at hseg
      obtain ⟨ti, hipos, hit, hiGuard, hiEnd⟩ := hclean 3 (stepWord g P)
        (fun _ => []) (fun n => aI * (n + 1) ^ dI) (by simpa [M] using hI) x
        (verdictWord acc (pairEncode x s)) []
      change H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 3) (stateWord (K + 1)
        (verdictWord acc (pairEncode x s)))) ti = Cfg.ofWords (hostRet M 3) (stateWord (K + 1)
          (stepWord g P (verdictWord acc (pairEncode x s)))) at hiEnd
      rw [hostRet_three, stepWord_verdictWord] at hiEnd
      have hiB := ModuleHost.request_budget aI dI D (2 * x.length + 2 + P.eval x.length + 5)
        (verdictWord acc (pairEncode x s)).length (by dsimp [D]; omega) (by omega)
      have hall : H.tm.runFrom (Cfg.ofWords (input := x) (ModuleHost.entry M 2)
          (stateWord (K + 1) (pairEncode x s))) (tv + 1 + ti) =
          Cfg.ofWords anchor (stateWord (K + 1) (step g P x (pairEncode x s))) := by
        rw [MultiTapeTM.runFrom_add, hseg, hiEnd]
      have hallGuard : ∀ v < tv + 1 + ti, (H.tm.runFrom (Cfg.ofWords (input := x)
          (ModuleHost.entry M 2) (stateWord (K + 1) (pairEncode x s))) v).state ≠ some anchor :=
        ModuleHost.guard_add H.tm anchor _ _ (tv + 1) ti hsegGuard hseg
          (fun v hv => hiGuard v hv 0)
      refine ⟨tv + 1 + ti + 1, by omega, ?_, ?_, ?_⟩
      · dsimp only [T, A, pow]
        simp only [Nat.add_mul]
        dsimp only [pow] at hpow'
        omega
      · intro v hv hvt
        have hvform : v = (v - 1) + 1 := by omega
        change (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
          (pairEncode x s))) v).state ≠ some anchor
        rw [hvform, MultiTapeTM.runFrom_succ_eq_step, hdisp]
        exact hallGuard (v - 1) (by omega)
      · rw [pairSndD_pairEncode, if_neg hb]
        change H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord (K + 1)
            (pairEncode x s))) (tv + 1 + ti + 1) =
          Cfg.ofWords anchor (stateWord (K + 1) (step g P x (pairEncode x s)))
        rw [MultiTapeTM.runFrom_succ_eq_step, hdisp, hall]
  have hFuel : F.ComputesFunInTime (fun x => Nat.bits (R.eval x.length)) T := by
    intro x
    apply (hF x).mono
    have h := ModuleHost.request_budget aF dF D (2 * x.length + 2 + P.eval x.length + 5) x.length
      (by dsimp [D]; omega) (by omega)
    have hp := hpow x.length
    dsimp only [T, A, pow]
    simp only [Nat.add_mul]
    dsimp only [pow] at hp
    omega
  obtain ⟨L, c, hL⟩ := FinTM.exists_loopFindTM H F anchor (Inv P) (step g P)
    (fun _ w => acc (pairSndD w)) (fun _ w => out (pairSndD w)) (fun x => pairEncode x x)
    (fun n => R.eval n) T hFuel
    (fun x => inv_init P x (by simpa using horbit x 0 (Nat.zero_le _)))
    (fun x w h => inv_step g P x w h) hstart hround
  obtain ⟨CP, cP, hCP⟩ := P.eval_le
  obtain ⟨CR, cR, hCR⟩ := R.eval_le
  refine ⟨L, c * (A * (CP + 7) ^ D + 1) * (CR + 2), (cP + 1) * D + cR, fun x => (hL x).mono ?_⟩
  exact final_bound c A D CP cP CR cR x.length (P.eval x.length) (R.eval x.length)
    (hCP _) (hCR _)

end Complexity.IterateFind
