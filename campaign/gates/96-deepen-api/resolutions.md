# Gate 96 (the deepening API, #196): resolutions

**Staged (2026-11-05)** on the exchange at `arora-barak-ch3-4/outbox/gates/96-deepen-api-gate/`
(exchange commit `f755a879`): bundle `96-deepen-api-bundle.md`, 209 sections, SHA-256
`1954b449d5347f77c72e6f294b608876d53145ff52a28f035e5d279c26e5c797`. Lean files from the PR head
`89f4ebbc6b0d007c981f907e3353d72fa84fa787`, everything else from the records commit
`683e2adf571e8b6a5c62280d4a3739ec89687546`. Findings file `deepen-api-findings.md`.

**Replay (2026-11-05): `replay-ldwa` passed**, 73 modules, 0 failed; the static check 0
mismatches, the campaign's existing 30 `sorry`s (`evidence/merged-tree/`).

#196 is clear to merge once gate 96 closes with zero blockers and zero majors.

**Dispatched (2026-11-05, the user).**

**Maintainer's supplementary check (after staging):** the pack cites four files outside the
18-file screen population (`Simulation`, `ARMLoops`, `ARMProof`, `Codec/Langs`). A screen widened
to 29 files and restricted to pairs touching the PR's files finds no pair beyond the pack's
`NoEdge`/`Rel` idiom (`evidence/screen/supplementary-29files/`).

## Round 1 findings (received 2026-11-05)

`findings.md`, verbatim from the exchange inbox (`arora-barak-ch3-4/inbox/deepen-api-findings.md`,
exchange commit `ad00d747c47c5cdbe3c1453fc49e07e553d084e2`), SHA-256
`5654d6d08d041ef16ada0c76b5360dd64bf7349d39a371debed8754c1e5da982`.

**Verdict: does not close.** 0 blockers, 2 majors (F1, `NoEdge` without its `_iff`; F2,
`Cfg.InWindow.apply_of_lt` re-derives `CfgRecord`'s private `recordStep_window`), 4 minors
(F3–F6), 6 notes (F7–F12). Dispositions follow below as the repairs land.

**Not yet clear to merge: #196** (gate 96 has two majors open).

## Round 1 dispositions (the repair commit `b1b5199bd946df834e38eefe4e58600f59a1a01b`)

| # | Severity | Disposition |
|---|---|---|
| 1 | major | **Repaired.** `noEdge_iff : NoEdge N x s w ↔ ¬ ∃ u < 2 ^ w, … ∈ initLang N ∧ ∃ v < 2 ^ w, … ∈ edgeLang N ∧ Reach (2 ^ w) (StepRel N x s) w u v`, by `Iff.rfl`, beside `NoEdge`, with a docstring stating the formula. The block-fit probe is extended to derive both loop steps (exit `false` ⇒ window exactness; `sp \|x\| < s` ⇒ exit `false`) from `fit_edge_block`, `noEdge_iff`, `noEdge_of_lt` and `mem_iff_reach_of_noEdge` with `NoEdge` sealed (`evidence/round2/route/`): `BlockFitDeepen` elaborates with 0 diagnostics; `NoEdge`'s controls 3 pass unsealed, 3 fail sealed; the fit's 55 controls 54 pass unsealed (`Reach`'s recursive delta goal fails) and 55 fail sealed. The optional `noEdge_iff_rcode` is not added: the fill needs only the two loop steps. |
| 2 | major | **Repaired, by the user's ruling (2026-11-05: harvest).** `CfgRecord`'s private `recordStep_window` is public as `Turing.Cfg.InWindow.apply_iff`, over any alphabet and state type, beside the definition, with `Turing.Cfg.InWindow.mono`; `apply_of_lt` is proved from the two; the record step cites `hc.apply_iff`. **The family is acknowledged by kind (the user, 2026-11-05):** "every proof that one action keeps a configuration in a window, and window monotonicity", canonical statements `Cfg.InWindow.apply_iff` and `Cfg.InWindow.mono`, paid back in the 12.2c window (`duplication-ledger.md`, WS-1; members found: on `Cfg.InWindow`, `ExpBFS.inWin_mono`, `ExpBFS.inWin_stepWith`, the window half of `Codec.boundary_iff`, `TQBF.codec_step_blank` and `ExhaustiveReplay.xr_window_stepWith`; over other window shapes (the widening), `FinTM.source_bounds`, `OracleTM.step_radius`, `dgWindow_step` and `emCall_track_support`/`_extent`; the tape half is a third canonical statement for 12.2c (`evidence/round2/window-family-members.md`)). |
| 3 | minor | **Fixed, within decision 4.** `PathWalk` gains the fourth `Iff.rfl` equation of decision 4 as `walkLe_succ_iff_head` (the head form; `walkLe_succ_iff` is taken by `ISCount`). `chain_of_walkLe` reads walks at the front, and `Reach` imports `PathWalk` instead of `ISCountMath`. `ISCount.walkLe_succ_iff` (proved by `simp only [WalkLe]` in a consumer file) is recorded as a 12.2c item. |
| 4 | minor | **Fixed.** `winRun_iff`, `rel_iff_orc`, `initO_iff_orc` and `accO_iff_orc` state their formulas; `Radius`'s module list names `winRun_iff` and `rcode_iff_reflTransGen`. |
| 5 | minor | **Fixed.** `Window`'s module docstring cites the deepening as [Sip13, §8.1, proof of Theorem 8.5] (Sipser, *Introduction to the Theory of Computation*, 3rd ed., 2013) and adds it to `## References`; `noEdge_of_lt` and `mem_iff_reach_of_noEdge` cite it, with the AB09 locations as "cf."; the facade reads "iterative deepening for Thm 4.14 without constructibility, after [Sip13, Thm 8.5]". The theorem number is the third edition's; the page was not checked against the book. |
| 6 | minor | **Fixed.** The screen is re-run with the pack's cited files in the population (`evidence/round2/screen/`): 32 files; base 711 declarations and 169 pairs, head 718 and 172; 3 new pairs, 0 gone: `Cfg.InWindow.mono` against `ExpBFS.inWin_mono` (WS-1) and the `NoEdge`/`Rel` idiom (QL-X1); the round-1 count gap is v3's 60-character cut-off. The inline-step sweep and the statement-shape search over every ref are recorded (`evidence/round2/sweep.md`, `evidence/round2/shape-search.md`): no added line re-derives a published lemma; no ref restates a new statement outside WS-1; the definitional reads the new equations can replace are RP-1 (12.2c). |
| 7 | note | **Docstring added:** `mem_iff_reach_of_noEdge` assumes neither `sp \|x\| ≤ s` nor a configuration-count bound. `mem_iff_reach`'s redundant `hcb` stays (frozen). |
| 8 | note | Recorded for the fill brief: the machine writes `rs, rw, rK, rU, rV, rM` in that order onto `fun _ => 0`. |
| 9 | note | Recorded; no change. |
| 10 | note | **Recorded for 12.2c (optional):** the window-run closure lemma. |
| 11 | note | **Ruled by the user (2026-11-05):** the `NoEdge`/`Rel` pair is an idiom (the query layout); **12.2c item opened:** codec-level query predicates, a `def` and an `_iff` lemma per query beside `initLang`/`acceptLang`/`edgeLang`. |
| 12 | note | **Errata recorded:** (a) BlockFitReal is sealed over 22 definitions, not 19; (b) `Reach` is sealed in its own home (disclosed only by `mkseal_dwa.py`); (c) the window seal omits `Cfg.workTapeSymbols`, `Cfg.inputSymbol` and `NDTM.CfgStep`, none of which is reduced; (d) the facade `SpaceComplexity.lean` imports the window module. |

**Replay of the repaired head:** `replay-ldwa2` passed, 73 modules, 0 failed, static 0 mismatches,
the existing 30 `sorry`s, chained from `oleans-cloud0` (`evidence/round2/merged-tree/`).

**Round 2 (2026-11-05):** `pack-r2.md`, at #196's head `ce9d63f4afcf549bff1bcb920254a8c05dc31d1c`.

**Round 2 staged (2026-11-05)** on the exchange at
`arora-barak-ch3-4/outbox/gates/96-deepen-api-r2-gate/` (exchange commit `dd3dad21`): bundle
`96-deepen-api-r2-bundle.md`, 149 sections, SHA-256
`0a6c59a30aab3354024cc792c9325e5d9ac9faa7c37fa8ce9878d9488b53a08b`. Lean files from #196's head
`ce9d63f4afcf549bff1bcb920254a8c05dc31d1c`, everything else from the records commit
`4558427c98b6205a3d5ed0d49251b5d3895b5cad`. Findings file `deepen-api-r2-findings.md`.

**Not yet clear to merge: #196** (gate 96's round 2 is staged, not yet dispatched).

**Round 2 dispatched (2026-11-05, the user).**

**Replay on the merged tree after #197 (2026-11-05):** `replay-ldwa3` passed (73 modules, 0 failed;
modules 73, mismatches 0, static total 30), at #196's head
`97adec6962e55c3a8ff191e602627674697fef18` (the campaign after #197 merged in; no file of the PR
changed), chained from `oleans-lzsa2` (`evidence/round2/merged-tree-after-197/`). It is the replay
of record for the merge while the campaign's Lean stays at #197's.

## Round 2 findings (received 2026-11-05)

`findings-r2.md`, verbatim from the exchange inbox (`arora-barak-ch3-4/inbox/deepen-api-r2-findings.md`,
exchange commit `bacfe4e2636a0d2a1b6f90da8a99d04719e597f1`), SHA-256 `f2d5a138512f8b515e9c0f652c08b985c028f48a87c0ff0592ff95f098dd6dfa`.

**Verdict: PASS.** 0 blockers, 0 majors, 1 minor (F1, accounting), 7 notes. Both round-1 majors are
resolved (notes 2–3), and minors 3–6 (notes 4–7).
