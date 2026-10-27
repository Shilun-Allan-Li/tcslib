<!-- DRAFT (maintainer, 2026-10-27), from `campaign/items/c1/c1e/H-route-design.md`, written with
that note's recommendations assumed (decisions 1–3 pending with the user). To fill at issue: every
⟨…⟩ from the pre-ship at the issue commit (@ANCESTOR@; the base's Lean content; the blob; the
in-flight list; the overlay's lines; the order list, roots and base sorry set; the probes' counts;
the screen base; the lint base). Then a review sub-agent, then issue. Remove this comment at
issue. -->

# Ch3–4 fill campaign — H, the nondeterministic time hierarchy (`Complexity.ntime_hierarchy`, `Diagonalization/NTimeHierarchy.lean`)

> **⟨Megafill …, item N⟩** (cover brief ⟨…⟩; addendum v2.5, Part 3). The preflight, the
> toolchain, the clone and the cache are done once for the session. For this item: create its
> branch from the shared base (below), make your first edit, **re-bootstrap your order list**, then
> follow this brief. **Budget:** ⟨the cover's⟩. Deliver a checkpoint zip after **each** checkpoint
> below, as soon as it is committed: the session may end at any time.

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **your target as a gated statement**: `Complexity.ntime_hierarchy`, the P3.3 statement gate
    (`campaign/gates/ch3-p33/`);
  - **the diagonalizer's contract** `Turing.NTimeDiag.exists_diagonalizer`
    (`Diagonalization/NTimeDiagonalizer.lean`; gate 39, restated with its decider hypothesis
    `hBF` at gate 45), **sorried** (the fill E-D, after E-Q);
  - **the decider, proved**: `Turing.exists_ndAcceptsWithin_decider` (your file), exactly the
    `hBF` hypothesis;
  - **the normal form's contract** `Turing.FinNDTM.exists_codeNDTM_accepts_linear`
    (`ClassNP/NDNormalForm.lean`; gate 38), **sorried** (the fill NF);
  - the stages' laws, proved (`NTimeDiagonalizer`): `ladder_succ`, `le_ladder`,
    `ladder_strictMono`, `two_mul_lt_ladder_succ`, `stage_spec`, `stage_eq`, `stageCode_eq`,
    `stageCode_frequently`, `budget_eq`; and `acceptLang_mem_NTIME`;
  - the fill-agent environment addendum `campaign/standards/fill-environment-addendum.md`
    (**v2.5**) and the copy-text screen v3 `scripts/copy-text-screen-v3.py`;
  - **this round's inputs** (`campaign/fills/h/inputs/h-fill-hierarchy/`): the overlay
    `NTimeHierarchyOverlay.lean.txt` (your file with region (a)'s import), the import probe, the
    route probe with its seal controls, the duplication probe and the screen population; the
    order list `campaign/fills/h/orders/h-fill-hierarchy.txt`, the base sorry set, the screen
    base and the pre-ship log (`campaign/fills/h/logs/h-fill-hierarchy-*`). The route's note is
    `campaign/items/c1/c1e/H-route-design.md`.
- **The environment was set up once, at the session's start** (the cover brief; Part 1 of the
  addendum and its Part 3). If Lean cannot start, Part 2 applies. **If Lean never runs, do not
  draft proofs blind.**
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/h-hierarchy @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  git rev-parse HEAD:TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean
  # must print a99d95dbe67c0419d8f410dfb1b0cd183ab80fac
  ```

  Record the base hash in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-h-hierarchy.zip`, with
  `REPORT.md` and the full modified source; a `git format-patch` series against your base and a
  git bundle whose only prerequisite is your base; the session's shared environment logs, this
  item's bootstrap and final sweep logs with **each module's time and maximum memory**, and the
  axiom log; the seal test's source, its controls and both outputs; both screen outputs; and
  `SHA256SUMS`.
- **Checkpoint zips.** After each checkpoint below, commit and write `fill-h-hierarchy-cp<N>.zip`
  with the same contents as of that commit. Deliver the latest if the session ends early.

## Base, line numbers and what lands around you

- **Your base's Lean content is ⟨BASE⟩** (at drafting: the campaign after #169, `94296486`). Lines
  in this brief are those of your base's tree, where `NTimeHierarchy.lean` is 1,793 lines (5 public,
  10 private by the lint's count).
- **Your first edit makes your file equal to the overlay**: one import,
  `import TCSlib.Complexity.Diagonalization.NTimeDiagonalizer`, after line 16 (region (a)). **Line
  numbers below are the base's; the overlay's are 1 more** (the target at 1723, overlay 1724).
- **In flight, merging after your base and invisible to it:** ⟨IN-FLIGHT; at drafting: E-Q's fill
  (megafill D's partial, under review, and its continuation) in `NTimeDiagonalizer.lean`, which adds
  that file's imports and privates; it changes no statement you cite⟩. Cite nothing they add.

## Parallel batches this round

None in `NTimeHierarchy.lean`. E-Q runs on its own branch in `NTimeDiagonalizer.lean`; E-D follows
it there. Neither changes a statement you cite.

## What this is

**The nondeterministic time hierarchy** [AB09, §3.2, Theorem 3.2] ([Coo72]): for
time-constructible `f`, `g` with every constant multiple of `f (n + 1) + f n + n + 1` eventually
below `g n`, `NTIME f ⊊ NTIME (g + 1)`. The statement and its docstring are **frozen verbatim**
(the docstring 1630–1722, the statement 1723–1726):

```lean
theorem ntime_hierarchy {f g : ℕ → ℕ} (hf : TimeConstructible f)
    (hg : TimeConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f (n + 1) + f n + n + 1) ≤ g n) :
    NTIME f ⊂ NTIME (fun n => g n + 1) := by
  sorry
```

**This brief supersedes the docstring's construction.** The sketch describes the diagonalizer
inline: the locator, the guess, the self-clocked mid-rung and the prefix clause. All of that is now
`exists_diagonalizer`'s contract, a separate fill. **Your proof is the chain only**, over that
contract. Its inclusion half, its thresholds and its chain are the docstring's "the chain, for the
alleged decider" and "inclusion". Do not edit the docstring before (d): the maintainer rewrites
the sketch at integration.

**Proved modulo, exactly:** `Turing.NTimeDiag.exists_diagonalizer` (and through it
`exists_queryTM`) and `Turing.FinNDTM.exists_codeNDTM_accepts_linear`. A complete delivery has no
admission of its own: the target's axiom walk reaches `sorryAx` only through those two.

**Read first:**
- the route note `campaign/items/c1/c1e/H-route-design.md`;
- `exists_diagonalizer`'s statement (its middle and top clauses, the order of `∀ α, ∃ C`, and the
  hypothesis `hBF`), `exists_codeNDTM_accepts_linear`'s, `exists_ndAcceptsWithin_decider`'s;
- `Complexity.NTIME`, `mem_NTIME_iff`, `NTIME.mono` (its truncation argument),
  `FinNDTM.DecidesInTime` with `decidesInTime_iff`, `FinNDTM.AcceptsWithin` with
  `acceptsWithin_iff` and `AcceptsWithin.mono`, `NDTM.HaltsWithin`, `NDTM.runWith_of_halt`;
- `ntime_hierarchy_of_pos`, right after your target (it consumes it unchanged).

**Pre-ship check** (the maintainer, at your base; its log is
`campaign/fills/h/logs/h-fill-hierarchy-preship.log`):
- **The overlay** elaborates with exactly your file's one sorry warning (overlay 1724). The
  import creates no cycle (`NTimeDiagonalizer`'s closure does not contain your file).
- **The import probe** (`HImportProbe.lean.txt`, **48 checks of 48 names**): 0 errors.
- **The route probe** (`HRouteProbe.lean.txt`, sealed over 4): `nh_chain` (the chain's induction),
  `nh_absorb` and `nh_inclusion` (the inclusion half, complete), `nh_top`, `nh_bottom`, `nh_middle`
  (the three thresholds) and `nh_stage` (a late stage of a code), each within the standard three.
  They may be copied into your home as `nh_` privates.
- **The seal controls** (`HSealControl.lean.txt`): every one closes unsealed and fails sealed.
- **The duplication probe** (`HDupProbe.lean.txt`): the chain, the absorption, the inclusion and the
  top threshold posed to `exact?`: 4 of 4 "could not close".

## Owned regions and targets (modify these and nothing else)

| # | File:line (base) | Target |
|---|---|---|
| 1 | `NTimeHierarchy.lean:1723` | `Complexity.ntime_hierarchy` (frozen statement) |

Your regions:
- **(a) the import**, as your first edit: exactly
  `import TCSlib.Complexity.Diagonalization.NTimeDiagonalizer`, after line 16. No other import.
- **(b) the home**, the blank line 1629 after `open Turing`, inside `namespace Complexity`: your
  `private` declarations, `private` only, and no `section`, `open` or `variable` that leaks past
  one.
- **(c) the body**, the `sorry` on line 1727.
- **(d) for a partial only, a paragraph headed `**Implementation status.**`** at the end of the
  target's docstring, before its ` -/` (line 1722). It is public-facing library text: what is
  proved and what is open, in mathematical terms, with no campaign labels and no dates. **Every
  new declaration has a docstring, and every proof over 20 lines a literal `**Proof sketch.**`
  paragraph** (`policy.md` §3).

**Not yours:** every other line (UN's `un_` privates, `exists_timed_universal_NDTM`,
`exists_ndAcceptsWithin_decider`, `ntime_hierarchy_of_pos`, `NTIME_linear_ssubset_square` and the
target's docstring before (d)), and every other file.

### Hosts (binding)

- **The diagonalizer:** cite `exists_diagonalizer` with `c` from
  `Turing.exists_effectiveNDMachineCode` and `hBF := Turing.exists_ndAcceptsWithin_decider c`.
  **Never build a machine**: no part of this proof constructs or runs one.
- **The normal form:** cite `exists_codeNDTM_accepts_linear`; the code `α` of its `M'` by the
  scheme's `decode_encode`.
- **Classes:** `mem_NTIME_iff`, `decidesInTime_iff`, `acceptLang_mem_NTIME`, `NTIME.mono`.
- **Leaves you may write:** the inclusion's finite absorption; the thresholds' arithmetic; the
  chain's induction; the two transfers (the middle's at `f (n + 1)`, the bottom's at `f a`). A
  further leaf is an escalation.

### The route (binding where it names a row)

Write `c` for the effective scheme, `D`, `K` for the diagonalizer and `L = {x | D.AcceptsWithin x
(K · (g |x| + 1))}`, so `L ∈ NTIME (g + 1)` (`acceptLang_mem_NTIME`, from `D`'s halting clause).

1. **The inclusion** (checkpoint 1): `NTIME f ⊆ NTIME (g + 1)`. `hfg` at `A = 1` gives `N₀` with
   `f n ≤ g n` for `n ≥ N₀`; with `F = 1 + Σ_{n < N₀} f n`, `c · f n ≤ c · F · (g n + 1)` for
   every `n`. The same machine decides at the larger budget: the transfer is `NTIME.mono`'s
   (pointwise `T₁ ≤ T₂`), at `T₂ n = F · (g n + 1)` with the constant folded by `mem_NTIME_iff`.
2. **The thresholds** (checkpoint 2): suppose `L ∈ NTIME f`, decided by `N` within `c₀ · f`. Take
   `M'`, `C₁` (normal form), `α` with `c.decode α = M'`, and `C` from `exists_diagonalizer` at `α`.
   Choose a stage `i` with `stageCode i = α` (`stageCode_frequently`) so large that, with
   `a = ℓᵢ + 1` and `T* = budget f ℓᵢ`:
   - for every `n` with `ℓᵢ < n`: `C · (C₁ · (c₀ · f (n + 1) + 1) + 1) ≤ g n` (`hfg` at a constant
     `A` with `A · (f (n + 1) + 1) ≥ C · (C₁ · (c₀ · f (n + 1) + 1) + 1)`, and `n > ℓᵢ ≥ i + 2`);
   - `C · 2^{C · (T* + 1)} ≤ 2^{T*²}`, that is the top's hypothesis at `n = ℓᵢ₊₁`
     (`ladder_succ`);
   - `C₁ · (c₀ · f a + 1) ≤ T* = (f a + a + 1)²` (`budget_eq`; once `a ≥ C₁ · (c₀ + 1)`).
3. **The middle step** (checkpoint 3): for `ℓᵢ < n < ℓᵢ₊₁` (so `n ≥ 3` and `stage f n = i`, by
   `stage_eq`): `1ⁿ ∈ L ↔ 1^{n+1} ∈ L`.
   - Forward: the middle's soundness gives `M'` accepting `1^{n+1}` within `g n`; the normal
     form's converse gives an accepting `N`-branch; `N`'s decision, with truncation to its
     all-branch budget (`NDTM.runWith_of_halt`, as in `NTIME.mono`'s proof), gives `1^{n+1} ∈ L`.
   - Backward: `N` accepts `1^{n+1}` within `c₀ · f (n + 1)`; the normal form gives `M'` within
     `t' = C₁ · (c₀ · f (n + 1) + 1)`; the first threshold gives `C · (t' + 1) ≤ g n`; the
     middle's completeness gives `1ⁿ ∈ L`.
4. **The chain and the contradiction** (checkpoint 4): by induction from `a` to `ℓᵢ₊₁`,
   `1^a ∈ L ↔ 1^{ℓᵢ₊₁} ∈ L`. The top's flip (the second threshold) gives
   `1^{ℓᵢ₊₁} ∈ L ↔ ¬ M'` accepts `1^a` within `T*`. The bottom's transfer (the third
   threshold, `AcceptsWithin.mono`, the normal form's converse and `N`'s decision) gives
   `M'` accepts `1^a` within `T*` iff `1^a ∈ L`. So `1^a ∈ L ↔ ¬ (1^a ∈ L)`.
5. **The target** (checkpoint 5): the inclusion and `L ∉ NTIME f` with `L ∈ NTIME (g + 1)` give
   the strict inclusion (`Set.ssubset_iff_subset_ne` or the definition of `⊂`).
6. **Edge cases that must stay true of your proof:** `f` or `g` with zeros (the absorption's
   `+ 1`); `n < 3` and the lengths at or below the seed `ℓ₀ = 2` (the stages start above it);
   `C = 0` or `C₁ = 0` (take `max 1`); `N₀ = 0`.

## Gate guidance (binding)

- **The P3.3 gate** (`campaign/gates/ch3-p33/`): the target's statement and the two declared addends
  of `hfg` (`f n` for the inclusion, `n + 1` for the middle's `1^{n+1}`).
- **Gate 39 and gate 45** (`exists_diagonalizer`): `∀ α, ∃ C` before the stage selection, so every
  threshold is chosen after `C`; the top's hypothesis is exactly the second threshold.
- **Gate 38** (`exists_codeNDTM_accepts_linear`): the linear transfer and its unbounded converse.

## Cited infrastructure (public and proved, or the two named contracts, at the issue commit)

All in `HImportProbe.lean.txt` (48 names): the target and its neighbour `ntime_hierarchy_of_pos`;
`exists_diagonalizer`, `exists_queryTM`, `exists_ndAcceptsWithin_decider`,
`exists_timed_universal_NDTM`; the normal form and the scheme; the stages' definitions and laws;
`NTIME` and its API; `DecidesInTime`, `AcceptsWithin`, `HaltsWithin` with their unfolding lemmas and
monotonicity; `runWith_of_halt`, `runWith_append`; and the core and Mathlib facts the route probe
uses.

## Ground rules (binding)

1. **File ownership, by region.** Only regions (a)–(d) of `NTimeHierarchy.lean`. List every new
   declaration with its role.
2. **Statement freeze** over the target and every landed public declaration.
3. **No new public declaration.**
4. **Escalation, item by item:** on anything unprovable as stated, stop **on that item only**,
   record the obstruction mathematically, and continue with every item that does not depend on
   it.
5. **No touching other sorries.** Cite `exists_diagonalizer` and `exists_codeNDTM_accepts_linear`
   as statements; never re-prove them or their parts.
6. **Imports.** Exactly the one of region (a).
7. **One proof per shared argument.** Never re-walk `NTIME.mono`'s truncation or
   `ntime_hierarchy_of_pos`'s rescaling; cite them or the lemmas they use.
8. **Size.** No cap. Report the final line count and the declaration counts.
9. **Continuation budget.** A partial zip states the checkpoints reached, the open declarations
   (each with a literal "Proof sketch") and the target's axiom walk.
10. **The pinned base, and no unfolding (user, 2026-10-16).** Never unfold a definition of
    another file, and no definitional closure either: `NTIME` through `mem_NTIME_iff`,
    `DecidesInTime` through `decidesInTime_iff`, `AcceptsWithin` through `acceptsWithin_iff`,
    `HaltsWithin` through `haltsWithin_iff`, `TimeConstructible` through `timeConstructible_iff`
    if at all, `budget` and `ladder` through `budget_eq`, `ladder_succ`, `ladder_zero`, `stage` and
    `stageCode` through their laws. Core and Mathlib definitions may reduce in `rfl`, `decide` or
    `show`, but are never passed to `simp`, `rw` or `unfold`. **Self-check by a seal test with
    controls** (each sealed definition: a goal closing by `rfl` unsealed and failing sealed),
    starting from the pre-ship's list, and an inspection table of your `rw`/`simp` arguments.
    Ship the raw outputs.
11. Keep your new privates under the `nh_` prefix (unused in the tree at the drafting base). Cite no
    private declaration of another file.

### Checkpoints (for a partial; ground rule 9)

The route's 1–5. Each may land alone. Add no new admission.

## Duplication governance (binding)

Run the text screen **before and after**, one run at a time, under `nice -n 10`.
- **The population** (`campaign/fills/h/inputs/h-fill-hierarchy/screen-population.txt`, 11 files):
  your file; `NTimeDiagonalizer`, `ClassNP/NTIME`, `ClassNP/NDNormalForm`, `NDCodes`,
  `Nondeterministic`; and the hazards `TimeHierarchy/Diagonal` (`time_hierarchy`'s absorption and
  chain), `SpaceComplexity/Hierarchy` (the space hierarchy's), `ClassP/DTIME`,
  `TimeHierarchy/Separation`.
- **The base** is `campaign/fills/h/logs/h-fill-hierarchy-screen-base.txt`: 102 declarations, 6
  pairs (MEASURED at your base; seconds). Your file has no pair.
- **No new cross-file pair** with an owned-file declaration on one side. **Known hazards:**
  `time_hierarchy`'s finite absorption (cite a published form if the pre-ship finds one);
  `NTIME.mono`'s truncation (cite).
- List every new in-file pair with a one-line justification. `REPORT.md` carries **"new copies:
  none"** (or lists each pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; the cache for the queue's Mathlib roots only (your order list's
  modules import 33 roots); **never `lake build`**, never the unfiltered `lake exe cache get`. Use
  `scripts/lean_check_tree.sh` for every check, one Lean process at a time.
- **Re-bootstrap** from `campaign/fills/h/orders/h-fill-hierarchy.txt` (**81 modules**, on the
  overlay) after your first edit, logging each module's time and maximum memory. **The base
  sorry-warning set has 22 entries in 11 modules**. Yours is `NTimeHierarchy`'s one.
- **Final checks:** `NTimeHierarchy`: zero errors, **no sorry warning** (for a partial, exactly the
  target's); every other module of the order list: sorry warnings exactly the base's minus yours;
  the import probe re-run, extended by your citations.
- **Axiom prints** for the target and every new private: within the standard three plus
  `sorryAx` only through the two named contracts; show the walk.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/Diagonalization`, 0 FAIL
  (base: 0 FAIL, 2 WARN over 5 files).

## Out-of-scope sorries you will see (leave every one untouched)

Everything in the base sorry set except your target: `exists_queryTM` and `exists_diagonalizer`
(`NTimeDiagonalizer`) and `exists_codeNDTM_accepts_linear` (`ClassNP/NDNormalForm`), which you cite
as statements; MIG-1 stage S's sorried specs (`Simulation`, `Composition`, `Encoding`,
`ClassP/TimeConstructible`, `Build/Wrappers`, `Build/Loop`, `Build/Primitives`); and
`CodeSimulator`'s `exists_uniformSimulator` (B5a).

## REPORT.md checklist

- [ ] The shared preflight and cache numbers, the shared logs copied into this zip, this item's
      bootstrap with per-module time and memory, and the base blob check.
- [ ] The overlay as the first edit; nothing else outside regions (b)–(d).
- [ ] The checkpoints reached, one zip each; the base hash and the ancestor check.
- [ ] Every new declaration with its role; the thresholds' constants; a proposed
      `**Implementation.**` paragraph for the target's docstring (public-facing).
- [ ] Rule 10: the declarations cited outside your file, the probe re-run, the seal with its
      controls and raw outputs, the inspection table.
- [ ] Duplication: both screens, every new pair justified.
- [ ] File size; the final sweep; every axiom print and the walk; the lint lines.

## Known pitfalls at this pin (hard-won)

- **`L`'s budget is `K · (g |x| + 1)`**, not `g |x| + 1`: membership is
  `D.AcceptsWithin x (K * (g x.length + 1))` by definition of the set.
- **`N`'s acceptance at an unbounded time** (the normal form's converse) must be truncated to its
  all-branch budget before `N`'s decision applies: `NDTM.runWith_of_halt` (as `NTIME.mono`'s proof
  does).
- **The stage's ends:** `stage f n = i` holds exactly for `ℓᵢ < n ≤ ℓᵢ₊₁` (`stage_eq`); the
  middle clause needs `n ≠ ℓᵢ₊₁`, the top clause `n = ℓᵢ₊₁`.
- `omega` with products and powers as atoms (`ring` first); the exponential threshold through
  `Nat.lt_two_pow` and `Nat.pow_le_pow_right`.
