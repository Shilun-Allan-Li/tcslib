**Verdict: issue after edits.** One major (F1, the truncation's host) and one decision on it (D1).
Apply `suggested-fix.diff`, which assumes D1 (A) and D2 (A), and re-run the pre-ship at the issue
commit. No prerequisite PR is needed.

# Review: the H fill brief draft (`h-fill-hierarchy.DRAFT.md`, `Complexity.ntime_hierarchy`)

This is a read-only review by the maintainer's review sub-agent, 2026-10-27.

**Scope.**
- The draft is `campaign/fills/h/drafts/h-fill-hierarchy.DRAFT.md` (blob `1292188e`, SHA-256
  `b8f319e7…799e`), unchanged at the campaign tip. **During the review #170 merged**: the tip moved
  from `6dbd74b9` to `ba2441f7`, whose TCSlib tree is #170's head's (`b703bccb`). The draft and the
  population are unchanged there, and the diff applies there.
- Its pre-ship is `preship-9d0af8cb/`. Its design note is `campaign/items/c1/c1e/H-route-design.md`.
- The base is #169's head `9d0af8cb`. Its TCSlib tree `3fce61e7` equals that of #169's merge
  `94296486` and of the tip before #170 (`out/00-bases.txt`). The snapshot is `oleans-laplusm`
  (before #170). The lists were also recomputed from the post-#170 tip (`out/lists-at-170.txt`).

**Method.**
- Lean ran only through `tools/leanelab.sh`, one elaboration at a time from this review. It ran in
  the review worktree `wt/`, detached at `9d0af8cb`, with `.lake/packages` symlinked after checking
  it was absent. Probes sat in `wt/rvprobe/` (untracked) and are copied to `probe/`.
- Every `.out` in `out/` is raw output with the worktree path stripped. Its last line gives the exit
  status, the wall time and the peak memory.
- The copy-text screen was not run. The draft, the notes and the records were treated as data.
- The repository, `wt-hk` and `exchange/` are untouched.

**Summary.**
- **The route is sound and complete.** The review proves the target's exact statement over the two
  cited contracts, sealed over 12 definitions, with `sorryAx` only through
  `exists_diagonalizer` and `exists_codeNDTM_accepts_linear`. The proof also holds in the home:
  both imports, the privates at (b), the body at (c), and **no diagnostic in the file** (`out/NTimeHierarchyFilledA.out`).
  The whole proof is about 170 lines.
- **The drafted parts hold up:**
  - the statement is byte-identical to the file;
  - every line number and region is right;
  - the overlay, the 48-name import probe, the route probe, the 4 seal controls and the duplication
    probe all reproduce exactly;
  - the order list, the 33 roots and the 22-entry sorry set check against the base tree (after
    #170: the same 81 modules and 33 roots, but 21 sorries in 10 modules, and the order must be
    re-sorted, F5);
  - the lint base reproduces.
- **What blocks a clean issue:** the one step the route needs and the brief does not host, the
  truncation of an unbounded acceptance to `N`'s all-branch budget (F1). The other findings are
  wording, lists and pitfalls.

## Checks

| # | Check | Result | Evidence |
|---|---|---|---|
| 1 | Bases | `9d0af8cb`, `94296486` and the tip `6dbd74b9` share the TCSlib tree `3fce61e7`. Owned blob `a99d95db…` (the brief's full hash is right), `NTimeDiagonalizer` blob `3cdc4f33`. #169's merge is an ancestor of the tip and of both PRs, and neither PR changes either blob. #170 has merged since (tip `ba2441f7`, TCSlib tree `b703bccb`, the owned and `NTimeDiagonalizer` blobs unchanged). | `out/00-bases.txt`; `git rev-parse ba2441f7:…` |
| 2 | Target, docstring, regions | The brief's quote equals lines 1723–1727 byte for byte. Docstring 1630–1722, with its ` -/` inline at the end of 1722 (region (d) goes before it, on that line). Home 1629 (blank, after `open Turing` at 1628). `sorry` 1727. Line 16 is the last import. 1,793 lines. | `out/statement-regions.txt` |
| 3 | Owned file at the base | exactly `1723:8` sorry, exit 0 | `out/elab-NTimeHierarchy-base.out` |
| 4 | Overlay (one import) | exactly `1724:8` sorry, exit 0. The closure is 62 modules; its only `Diagonalization` modules are the two (and `Uncomputability/Diagonalization`), so no cycle. | `out/NTimeHierarchyOverlay.out`, `out/closure.txt` |
| 5 | Import probe | **48 of 48**, 0 errors, 4 prints within the standard three | `out/HImportProbe.out` |
| 6 | Route probe | 7 prints, all within `[propext, (Classical.choice,) Quot.sound]`, no other output | `out/HRouteProbe.out` |
| 7 | Seal controls | exactly 4 errors, at sealed lines 42, 47, 53 and 58; the unsealed section closes | `out/HSealControl.out` |
| 8 | Duplication probe | 4 of 4 "could not close" | `out/HDupProbe.out` |
| 9 | **The whole chain** | `nh_target` (the target's statement) proved over the two contracts, sealed over 12. Its walk: `sorryAx` directly in exactly `exists_codeNDTM_accepts_linear` and `exists_diagonalizer`. The truncation through the published `runWith_*` lemmas uses one import (`HReviewProbe`); through `run_take_of_halted` it uses two (`HChainProbe`). | `out/HReviewProbe.out`, `out/HChainProbe.out` |
| 10 | The chain in the home | both imports, the 9 privates at (b), the body at (c): **0 diagnostics**, exit 0. `ntime_hierarchy`, `ntime_hierarchy_of_pos` and `NTIME_linear_ssubset_square` all walk to exactly the two contracts. | `out/NTimeHierarchyFilledA.out` |
| 11 | Two-import overlay (D1 (A)) | exactly `1725:8` sorry, exit 0. `ChoiceWords` imports only `Mathlib.Order.Monotone.Basic`, `Data.List.TakeDrop` and `Tactic.Ring`, all among the 33 roots. It is already 46th in the 81-module order list, ahead of the owned file (80th). | `out/NTimeHierarchyOverlay2.out`, `out/lists-check.txt` |
| 12 | Review seal controls | the 8 further definitions (`NDTM.runWith`, `NDTM.initCfg`, `ladder`, `budget`, `stage`, `stageCode`, `TimeConstructible`, `CodeNDTM.toFinNDTM`): exactly 8 errors at sealed lines 50–74; the unsealed section closes | `out/HReviewSealControl.out` |
| 13 | Import probe, extended | **70 of 70** (the 48 plus the review proof's 22 further citations), two imports, 0 errors; `run_take_of_halted` on `[propext]` | `out/HImportProbeExt.out` |
| 14 | Review duplication probe | the truncation, its decider corollary, `nh_bottom`, `nh_middle` and `nh_stage`: 5 of 5 "could not close" | `out/HReviewDupProbe.out` |
| 15 | Lists | The order list (81) is the `Diagonalization` facade's closure. Its direct Mathlib imports are exactly the 33 roots. A textual sorry count gives 22 in the same 11 modules, matching module by module. **At the post-#170 tip:** the same 81 modules and 33 roots; 21 sorries in 10 (`CodeSimulator`'s gone); the pre-ship's order is no longer topological, because `CodeSimulator` now imports `Build/InterpreterStartup`, which the list places later. | `out/lists-check.txt`, `out/facade-closure.sorted`, `out/lists-at-170.txt` |
| 16 | Lint | base `0 FAIL, 2 WARN over 5 files` (identical to the pre-ship's). With the review's proof in place: `0 FAIL, 2 WARN`, 1,963 lines, 5 public / 19 private. | `out/lint-base.txt`, `out/lint-filled.txt` |
| 17 | Rule 10 | Every other-file definition is read through a published lemma. The review proof's `rw`/`simp` arguments (inspection table below) are lemmas only; no `unfold`. | `probe/HChainProbe.lean` |
| 18 | Duplication search | See F1–F3 and the notes. No published chain, absorption, threshold or truncation-of-acceptance in the tip, #170 (`79efb462`), #171 (`d17f63c8`) or `origin/main` (whose `ntime_hierarchy` is the same statement, sorried). The nearest Mathlib form of the chain, `Nat.rel_of_forall_rel_succ_of_le_of_le`, needs the step at every `n ≥ a`, not only below `b`, so `nh_chain` stays. | greps in this review; Mathlib `Order/Monotone/Basic.lean` 531 |
| 19 | Copy-text screen | not run. The population changes (F3), so the base is re-measured at issue. | — |

**The review proof's rule-10 inspection table** (from `probe/HChainProbe.lean`):

| Tactic | Arguments | Kind |
|---|---|---|
| `simpa only` | `Nat.mul_assoc` | core lemma |
| `rw` | `← pow_add` | Mathlib lemma |
| `simp only` | `NDTM.runWith_append w w' _`, `NDTM.runWith_of_halt _ h` | published lemmas |
| `change`, then `rw` | `List.length_replicate` | `Language`/`setOf` reduce in `change` (Mathlib, allowed); core lemma |
| `rw … at hC` | `c.toNDMachineCode.decode_encode M'` | published lemma |
| `rw` | `NTimeDiag.budget_eq` (twice), `NTimeDiag.ladder_succ f i` | published equations |
| `rwa … at h` | `List.length_replicate` | core lemma |
| `rw` | `hs`, `hmemL` | local hypotheses |

**Commands.** Each was run alone, from `wt/`, with `S` the scratchpad:
`bash $S/tools/leanelab.sh $S/review/h-brief/wt $S/oleans-laplusm rvprobe/<F>.lean`, through
`scripts/run-preship.sh <F>`. The files `<F>` were:
- `NTimeHierarchyOverlay`: exit 0, 1 warning;
- `HImportProbe`: exit 0;
- `HRouteProbe`: exit 0, 7 prints;
- `HSealControl`: exit 1, 4 errors;
- `HDupProbe`: exit 1, 4 "could not close";
- `HReviewProbe`: exit 0, 3 prints, 3 walks;
- `HChainProbe`: exit 0, 3 prints, 3 walks;
- `HReviewSealControl`: exit 1, 8 errors;
- `NTimeHierarchyOverlay2`: exit 0, 1 warning;
- `NTimeHierarchyFilledA`: exit 0, 3 prints, 3 walks, no other output;
- `HImportProbeExt`: exit 0;
- `HReviewDupProbe`: exit 1, 5 "could not close";
- `HReviewPitfalls`: exit 1, the unknown constant;
- `HReviewPitfalls2`: exit 1, (a) fails and (b) closes.

The owned file was also elaborated at the base. The lint was run as
`nice -n 10 python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/Diagonalization`, on the
tree and on a scratch copy with `NTimeHierarchyFilledA` in place (since removed).

## Findings

| # | Severity | Where | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| F1 | **major** | Route step 3 (forward) and step 4 (bottom); hosts' leaf list; ground rule 7; pitfall 2; hazards | **The truncation has no licensed host, and the brief contradicts itself on it.** Both the middle's forward step and the bottom's transfer need `N.AcceptsWithin x t' → N.AcceptsWithin x (c₀ · f \|x\|)` from `N`'s all-branch halting, because the normal form's converse is unbounded. The brief says to do this with `NDTM.runWith_of_halt` "as `NTIME.mono`'s proof does". Rule 7 says "Never re-walk `NTIME.mono`'s truncation", and the leaf list ("a further leaf is an escalation") has no truncation leaf. There is no published truncation of *acceptance* in the closure: `NTIME.mono` does it inline (`NTIME.lean` 223–233). The shared form, `Turing.run_take_of_halted` (`TuringMachine/ChoiceWords` 99–116, "factored … replacing three private copies"), is **outside the one-import closure**. Two private copies of exactly the lemma needed already exist: `ExhaustiveReplay`'s `xr_accepts_iff_of_halts` (134, in the closure) and `Nondeterminism`'s `acceptsWithin_iff_of_halts` (164). Neither file is in the screen population. As drafted, the agent must either break rule 7, write an unlicensed leaf (escalation), or make an unscreened third copy. | `out/closure.txt` (62 modules, no `ChoiceWords`); `HChainProbe`: the truncation in 6 lines through `run_take_of_halted` with a second import; `HReviewProbe`: the same through `runWith_append`/`runWith_of_halt` with one import; both feed `nh_target` (`out/HChainProbe.out`, `out/HReviewProbe.out`) | **D1.** The diff (A): a second import, `TCSlib.Complexity.TuringMachine.ChoiceWords` (no cycle, no new root, order list unchanged, overlay offset +2, target at 1725), and the licensed leaf `nh_accepts_of_halts` through `run_take_of_halted` with `nh_mem_of_accepts`. Rule 7, the hosts, steps 3–4, the pitfall and the hazards are rewritten to match. |
| F2 | minor | Ground rule 7 | "Never re-walk … `ntime_hierarchy_of_pos`'s rescaling; cite them" cannot be met. That rescaling is inline inside a consumer of the target (`hback`). There is no `NTIME.mono_const`, although `SPACE.mono_const` and `NSPACE.mono_const` exist. The brief's own licensed `nh_inclusion` repeats the fold (`refine ⟨a * F, N, …⟩; simpa only [Nat.mul_assoc]`). | `NTimeHierarchy.lean` 1740–1752; `SpaceComplexity/Basic.lean` 179; `Machines/NARMProof.lean` 60; `HRouteProbe` 52–63 | Diff: write the fold once (`nh_inclusion`) and disclose its in-file pair. |
| F3 | minor | Duplication governance; `screen-population.txt` | The population omits `ChoiceWords` (cited under D1 (A)) and the truncation's two private copies, `ClassNP/ExhaustiveReplay` and `ClassNP/Nondeterminism`. The memory rule "screen populations cover citations" applies. The prose also omits `ClassP/TimeConstructible`, which the file lists. | `orig/screen-population.txt` (11 files) | Diff: 14 files (the population file too). Re-measure the base at issue. The hazards name the two private copies. |
| F4 | minor | Ground rule 10; pre-ship's seal | Rule 10 names nine definitions (adding `TimeConstructible`, `budget`, `ladder`, `stage`, `stageCode`). The pre-ship seal and controls cover 4. The chain also reads `NDTM.runWith`, `NDTM.initCfg` and `CodeNDTM.toFinNDTM`. Starting "from the pre-ship's list" under-seals. | `out/HReviewSealControl.out` (8 more controls, each failing sealed only); `HChainProbe` passes sealed over 12 | Diff: start from the chain probe's 12; stage `HReviewSealControl.lean` as `HChainSealControl.lean.txt`; rule 10 says how `runWith` and `toFinNDTM` are read. |
| F5 | minor | In-flight list; parallel batches | The list names only E-Q's fill ("megafill D's partial, under review"). That text is stale: E-Q's checkpoint 1 is reviewed, and its landing is prepared on #171, local only. Cont1 is a separate Claude fill. The list omits #170 and #171. **#170 merged during this review** (`ba2441f7`). It touches `CodeSimulator`, in the closure: it proves `exists_uniformSimulator`, so the sorry set becomes 21 in 10 modules, and its new import of `Build/InterpreterStartup` makes the pre-ship's order non-topological. It also touches `EXPCOM`/`Relativization` (order list, via the facade). The base line, the sorry count and the out-of-scope list must follow. #171 adds `Build/WordTests`, which enters the closure through `TMSAT`. E-Q's landing adds eight imports to `NTimeDiagonalizer`: `Mathlib.Data.Nat.Log` (a new root) and `Build/Contract/Catalog`/`Contract/Seam` (new to the order list). After #171 and E-Q the closure is 65 modules (from 62) and the order list 84. None changes a cited statement. | `out/00-bases.txt`, `out/lists-at-170.txt`, `out/closure-eqland.sorted` (at `27ca2927`) | Diff: #170 as merged (base line, ⟨21 in 10⟩, out-of-scope list, the re-sorted order); the accurate in-flight list; the rule that every list is re-measured if #171 or E-Q merges first. |
| F6 | minor | Banner; ancestor list | "addendum v2.5" (twice). The addendum is v2.6, and the cover draft says v2.6. | `campaign/standards/fill-environment-addendum.md` line 1 at the tip | Diff. |
| F7 | minor | Pre-ship; cited infrastructure | The cover requires the import probe to cover "every external name the source cites". The route's citations go beyond the 48: `run_take_of_halted`, `Set.ssubset_iff_of_subset`, `List.length_replicate`, `toNDMachineCode`, `encode`, `Nat.le_self_pow` and more. | `out/HImportProbeExt.out` (70 of 70) | Diff: ⟨70⟩, two imports. Stage `HImportProbeExt.lean` as the import probe. |
| F8 | minor | Pitfalls | `Nat.lt_two_pow` does not exist at this pin. The probes use `Nat.lt_two_pow_self`. | `out/HReviewPitfalls.out` | Diff. |
| F9 | minor | Gate guidance | "`n + 1` for the middle's `1^{n+1}`" is wrong for this route. The middle's threshold uses `f (n + 1)` and the constant `1` (`nh_middle`: `f (n+1) + 1 ≤ f (n+1) + f n + n + 1`). The `n` addend covered the old construction's startup costs (P3.3 pack item 7), which are now inside `K`. | `HRouteProbe` 90–101; `ch3-p33/pack.md` 128–133 | Diff. |
| F10 | minor | "This brief supersedes…" | It says the docstring's chain survives. Its arithmetic does not: `A*`, the prefix clause, the `\|bits (g n)\|` term and `BF` against `K·(g n + 1)` are all superseded by the contract's `C · (t' + 1) ≤ g n` and top hypothesis. Only the inclusion and the shape (3.3)/(3.4) and the bottom's transfer remain. | `NTimeHierarchy.lean` 1694–1722 against `exists_diagonalizer` | Diff. |
| F11 | note | Comment | The placeholder list should name the staged review probes (the chain probe, its seal controls and duplication probe, the extended import probe). | — | Diff. |
| F12 | note | Pitfalls | Membership in `L` is `Language`'s own `∈` (`Mathlib/Computability/Language.lean` 61). `simp only [hL, Set.mem_setOf_eq]` makes no progress (the review's first attempt failed there). `show`, then `List.length_replicate`, closes it. A second pitfall: rewrite the decoded code once `C` is obtained. | `out/HReviewPitfalls2.out` ((a) unsolved with both simp arguments unused; (b) closes) | Diff: two pitfalls. |
| F13 | note | Hosts | `exists_effectiveNDMachineCode` is a `Nonempty` (`obtain ⟨c⟩`). `α = c.encode M'`, with `decode_encode` reached through `c.toNDMachineCode`. The Classes list lacks `acceptsWithin_iff`, `haltsWithin_iff` and `AcceptsWithin.mono`, which the route uses. `Set.ssubset_iff_of_subset` is the direct close. | `HChainProbe` 150–225 | Diff. |
| F14 | note | Size; the cover | The ESTIMATE of 800–1,500 lines (route note, cover) is about five times the measured proof. With the review's proof the file is 1,963 lines (+170: 2 imports, 97 lines of privates, a 71-line body). The cover's "a partial is fine" and the session budget are over-provisioned. | `out/lint-filled.txt` | D2; the cover is not in the diff. |
| F15 | note | Axiom prints | At the base `exists_diagonalizer` is a bare `sorry`, so "(and through it `exists_queryTM`)" does not show in the walk yet. The brief asks the agent to "show the walk" without a method. | `out/HChainProbe.out` (the walk) | Diff: name the chain probe's `rvSorryWalk`. |
| F16 | note | Route step 2 | Threshold 1's "`n > ℓᵢ ≥ i + 2`" is beside the point: what is needed is `ℓᵢ ≥ N₁`, which `nh_stage` gives. Threshold 2 does not say why `T*` is large: `T* ≥ ℓᵢ + 2` by `budget_eq`. Step 4's bottom omits the truncation. | `HChainProbe` 168–212 | Diff. |
| F17 | note | Edge cases | "`C = 0` or `C₁ = 0` (take `max 1`)": no `max` is needed. `nh_top`, `nh_bottom` and `nh_middle` hold at `0`, and `nh_target` uses no `max`. | `HChainProbe` | Diff. |
| F18 | note | Lint | The owned file already WARNs for size (1,793 > 1,000) and will at 1,963. Pre-disclose that this is expected (file size alone is not a driver). | `out/lint-filled.txt` | Diff. |

## Decisions for the user

**D1 (F1): how the truncation is hosted.**
- **(A) A second import, `TCSlib.Complexity.TuringMachine.ChoiceWords`, and one licensed leaf
  through `Turing.run_take_of_halted` (recommended).**
  - It is the shared form, factored at the wave-1 gate to replace private copies.
  - It imports only Mathlib, creates no cycle and adds no root. The order list keeps its 81 modules,
    with `ChoiceWords` already 46th.
  - The overlay moves by +2: the target goes to 1725, with exactly that sorry warning
    (`out/NTimeHierarchyOverlay2.out`). The leaf is 6 lines (`HChainProbe`).
  - The cover draft's "Its first edit: its overlay (one import, …)" becomes "two imports".
- (B) Keep the one import, and license an 8-line truncation leaf through `NDTM.runWith_append` and
  `NDTM.runWith_of_halt` (`HReviewProbe`'s `nh_accepts_of_halts`).
  - No import changes.
  - It is a third copy of the content of `xr_accepts_iff_of_halts` and `acceptsWithin_iff_of_halts`,
    to be disclosed as pairs. Rule 7's truncation clause would have to be withdrawn rather than
    rewritten.

**D2 (F14, checks 9–10): what to do with the review's complete proof.**
- **(A) Issue as ruled (Codex, megafill E), with the chain probe staged as an input that the fill
  may copy (recommended).**
  - This stays inside the 2026-10-27 ruling. The brief already lets the route probe's lemmas be
    copied.
  - The agent still owns the bootstrap, the sweep, the seal with controls, both screens, the axiom
    walk, the docstrings and `REPORT.md`.
  - The cover's budget and size line can shrink: about 170 lines, and checkpoints 2–5 become
    transcription.
- (B) Land the proof by a maintainer PR now, with a fill-style gate, and drop H from megafill E. This
  is the cheapest route: the review's file already elaborates in the home with no diagnostic. It
  departs from the ruled agent choice.
- (C) Issue as drafted, without the chain probe, so the agent derives the chain itself. The chain
  probe then serves only as the gate's reference. It costs a session for an argument already checked.

Everything else is a maintainer edit within the user's 2026-10-27 rulings: H now, the old sketch
superseded and rewritten at landing, Codex.

## What the diff changes

`suggested-fix.diff` makes 38 asserted replacements in the draft and adds 3 lines to
`screen-population.txt` (`scripts/apply_fixes.py`; `orig/` and `edited/` hold the files before and
after the edits). It assumes D1 (A) and D2 (A). It passes `git apply --check` in the records
worktree at the post-#170 tip `ba2441f7`, and applying it to that tip's two files reproduces
`edited/` exactly.

| Findings | Edits |
|---|---|
| F1 | region (a), the overlay line and offset, rule 6, the hosts (truncation; leaves), route steps 3–4, rule 7, the hazards, the pitfall, "Read first" |
| F2 | rule 7's fold clause |
| F3 | the population prose, the base placeholder and the hazards; the population file (+`ChoiceWords`, `ExhaustiveReplay`, `Nondeterminism`) |
| F4 | rule 10's list and its seal start (12); the pre-ship's seal line |
| F5 | the in-flight list, the parallel batches and the re-measure rule |
| F6 | v2.6, twice |
| F7 | the import probe's ⟨70⟩, the cited-infrastructure list |
| F8–F10, F12, F13, F15–F18 | as in the table |
| D2 (A) | the inputs list, "Read first", the pre-ship's chain-probe line and the REPORT checklist's "what you copied" |

**Not in the diff:**
- the cover draft `megafill-E.DRAFT.md` ("one import" under D1 (A); the size and budget lines,
  F14);
- the route note, whose hazard line has the same truncation wording as F1;
- staging the review's probes as inputs. The suggested names are:
  - `probe/HChainProbe.lean` → `HChainProbe.lean.txt`;
  - `probe/HReviewSealControl.lean` → `HChainSealControl.lean.txt`;
  - `probe/HReviewDupProbe.lean` → `HChainDupProbe.lean.txt`;
  - `probe/HImportProbeExt.lean` → the import probe;
  - `probe/NTimeHierarchyOverlay2.lean` → the overlay.

**At issue:** re-run the pre-ship on the issue commit, which is after #170, against a post-#170
snapshot (for example #170's replay snapshot `oleans-lb5am`, if it is that tree), not
`oleans-laplusm`. That covers:
- the overlay, both import probes, the route and chain probes, both seal-control files and both
  duplication probes;
- the order list, re-sorted; the roots; the base sorry set (expected 21 in 10); the 14-file screen
  base; the lint.

None of the cited statements changed with #170, so the probes are expected to reproduce. If #171 or
E-Q's landing has merged by then, F5 gives the further changes.

## Files

- `REVIEW.md` (this file), `suggested-fix.diff`.
- `out/`:
  - `00-bases.txt`, `statement-regions.txt`, `lists-check.txt`, `lists-at-170.txt`;
  - `closure.txt`, `closure.sorted`, `closure-eqland.sorted`, `facade-closure.sorted`,
    `order.sorted`;
  - `elab-NTimeHierarchy-base.out` and one `.out` per probe below;
  - `lint-base.txt`, `lint-filled.txt`.
- `probe/` (every Lean file run):
  - the pre-ship's five, re-run verbatim: `NTimeHierarchyOverlay`, `HImportProbe`, `HRouteProbe`,
    `HSealControl`, `HDupProbe`;
  - the review's: `HReviewProbe`, `HChainProbe`, `HReviewSealControl`, `HReviewDupProbe`,
    `HImportProbeExt`, `NTimeHierarchyOverlay2`, `NTimeHierarchyFilledA`, `HReviewPitfalls`,
    `HReviewPitfalls2`.
- `scripts/`:
  - `run-preship.sh` (the runner);
  - `closure.py` (import closure; it misses `TuringMachine/Configuration` through a header quirk,
    hence facade 80 against the order list's 81);
  - `mkfilled.py` (the home build, asserted) and `mkchain.py` (the chain probe, asserted);
  - `walk.lean.txt` (the axiom walk);
  - `apply_fixes.py` (the diff's edits, asserted).
- `orig/`, `edited/`: the draft and the population before and after the edits.
- `wt/`: the review worktree (detached at `9d0af8cb`, untracked `rvprobe/` only).
