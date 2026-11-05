# External audit pack, round 2: the deepening's API (PR #196, an API gate)

**Round 1** (`pack.md`; findings `findings.md`; resolutions `resolutions.md`) was **does not close,
0 blockers, 2 majors, 4 minors, 6 notes**. No statement was false; the majors were `NoEdge`
without its `_iff` (finding 1) and `Cfg.InWindow.apply_of_lt` re-deriving its own file's private
`recordStep_window` (finding 2). **Ruled (user, 2026-11-05):** repair in #196; **harvest**
`recordStep_window`; the window-step family **acknowledged by kind** and widened (WS-1); the
`NoEdge`/`Rel` pair an **idiom** (QL-X1), with a 12.2c item for codec-level query predicates
(CQ-1).

**The PR now:** #196 on `lean/deepen-window-api`, head `ce9d63f4afcf549bff1bcb920254a8c05dc31d1c`:
- `b1b5199bd946df834e38eefe4e58600f59a1a01b`, the repair (`evidence/round2/patches/`), which changes
  the PR's own ten files and no other;
- then a merge of the campaign, which changes no `.lean` file.

## What changed since round 1 (verify)

| Finding | Change |
|---|---|
| 1, `NoEdge` | `noEdge_iff : NoEdge N x s w ↔ ¬ ∃ u < 2 ^ w, … ∈ initLang N ∧ ∃ v < 2 ^ w, … ∈ edgeLang N ∧ Reach (2 ^ w) (StepRel N x s) w u v`, `Iff.rfl`, beside the definition. The block-fit probe is extended to the join (`evidence/round2/route/BlockFitDeepen.lean.txt`), below |
| 2, the window step | `CfgRecord`'s private `recordStep_window` is public as `Turing.Cfg.InWindow.apply_iff`, over any alphabet and state type, beside `Cfg.InWindow`, with the new `Turing.Cfg.InWindow.mono`. `apply_of_lt` is proved from the two (`((hC.mono hs).apply_iff a).mpr …`), and `recordStep_observed_action` cites `hc.apply_iff`. The harvested per-move step is `simp only` with the lemmas `simp?` reports (core and Mathlib only) |
| 3, `Reach`'s import | `PathWalk` gains `walkLe_succ_iff_head : WalkLe E n (j + 1) c t ↔ c = t ∨ ∃ v, v < n ∧ E c v ∧ WalkLe E n j v t` (`Iff.rfl`; decision 4's fourth equation, named apart from `ISCount.walkLe_succ_iff`). `chain_of_walkLe` reads walks at the front, by induction generalizing the start, and `Reach` imports `PathWalk` in place of `ISCountMath` |
| 4, the docstrings | `winRun_iff`, `rel_iff_orc`, `initO_iff_orc`, `accO_iff_orc` state their formulas; `Radius`'s module list names `winRun_iff` and `rcode_iff_reflTransGen` |
| 5, attribution | `Window` cites the deepening as [Sip13, §8.1, proof of Theorem 8.5] (in `## References`, the module docstring, `noEdge_of_lt` and `mem_iff_reach_of_noEdge`); the AB09 tags read "cf."; the facade reads "iterative deepening for Thm 4.14 without constructibility, after [Sip13, Thm 8.5]" |
| 6, the evidence | the v3 screen with the pack's cited files in the population, the inline-step sweep, and the statement-shape search over every ref (`evidence/round2/screen/`, `sweep.md`, `shape-search.md`, `window-family-members.md`) |
| note 7 | `mem_iff_reach_of_noEdge`'s docstring adds that no configuration-count bound is assumed |
| notes 10–12 | the ledger (WS-1, WC-1, QL-X1, CQ-1, RP-1) and the round-1 pack's errata (`resolutions.md`) |

**Freeze** (`evidence/round2/freeze/`, `declfreeze.py` from round 1's head `89f4ebbc` to
`b1b5199bd946df834e38eefe4e58600f59a1a01b`, each file with its authorized bodies): no statement
changed; public declarations added: `Cfg.InWindow.apply_iff`, `Cfg.InWindow.mono`,
`walkLe_succ_iff_head`, `noEdge_iff`; private removed: `recordStep_window`; bodies or docstrings
changed: `apply_of_lt`, `winRun_iff`, `rel_iff_orc`, `initO_iff_orc`, `accO_iff_orc`,
`noEdge_of_lt`, `mem_iff_reach_of_noEdge`, and the privates `recordStep_observed_action` and
`chain_of_walkLe`. The new names are unused on every ref.

## Brief for the auditor

1. **Finding 1:** does `noEdge_iff` state `NoEdge`'s body, and does the extended block fit derive
   both loop steps (exit `false` ⇒ window exactness; `sp |x| < s` ⇒ exit `false`) with `NoEdge`
   sealed?
2. **Finding 2:** are `apply_iff` and `mono` the right public forms, at the right generality? Is
   `apply_of_lt` now a corollary, and does any proof the PR adds still re-derive a window step?
3. **Finding 3:** is `chain_of_walkLe` correct, and does it read `WalkLe` only through
   `walkLe_zero_iff` and `walkLe_succ_iff_head` (the seal, below)?
4. **Findings 4–6:** are the docstrings, the attribution and the evidence right? Is
   [Sip13, §8.1, proof of Theorem 8.5] the right location? (The theorem number is the third
   edition's; the page was not checked against the book.)
5. **Further re-derivations** anywhere in the added lines, against the published API and the
   acknowledged families (WS-1 is acknowledged by kind, widened).

## Repository-side attestations (verify or challenge)

- **Elaboration:** the chain (`evidence/round2/chain/`): the PR's changed modules and every module
  on an import path between them (16, the facade apart), compiled in order into a copy of the
  first cloud snapshot `oleans-cloud0` (the campaign at `dfed8b1f`'s Lean tree): 0 errors; the only
  diagnostics are `RecordTable`'s 4 existing `sorry`s.
- **The join** (`evidence/round2/route/`): `BlockFitDeepen.lean.txt` (the round-1 fit, `NoEdge`
  added to its seal, and a sealed `Loop` section with `fit_edge_bit_eq_false_iff`,
  `deepen_step_exit_false`, `deepen_step_exit_of_lt`) elaborates with **0 diagnostics**. Controls:
  `NoEdge` 3 pass unsealed, 3 fail sealed; the fit's 27 sealed definitions 54 of 55 pass unsealed
  (the one failure is `Reach`'s delta goal, recursive) and 55 of 55 fail sealed.
- **Rule 10** (`evidence/round2/rule10/`, round 1's generator re-anchored): the window lemmas
  (`mono`, `apply_iff`, `apply_of_lt`), `Reach`'s two proofs, the register equations and the window
  module (whole file, `noEdge_iff` included) elaborate sealed with **0 diagnostics**; controls 26
  → 24 unsealed (`WalkLe`'s and `Reach`'s delta goals, recursive) → 0 sealed, as in round 1.
- **Axioms** (`evidence/round2/axioms/`): all seventeen public lemmas of the PR on subsets of
  `[propext, Classical.choice, Quot.sound]`.
- **Screen** (`evidence/round2/screen/`): 32 files (the round-1 18 and the pack's cited files);
  base 711 declarations and 169 pairs, head 718 and 172; 3 new pairs, 0 gone: `Cfg.InWindow.mono`
  against `ExpBFS.inWin_mono` (both directions; WS-1, acknowledged) and the `NoEdge`/`Rel` idiom
  (QL-X1). The round-1 counts (321 → 323) are explained by v3's 60-character cut-off.
- **Replay:** `replay-ldwa2` (`evidence/round2/merged-tree/`), the ten files' downstream closure,
  chained from `oleans-cloud0`: **73 modules, 0 failed**; the static check 0 mismatches, the
  campaign's existing 30 `sorry`s.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/96-deepen-api/findings-r2.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `deepen-api-r2-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
