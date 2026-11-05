# Gate 03l (the `Randomized/Build/` machine layer): round 1 resolutions

- **Round 1:** findings `findings/gate03l-findings.md`, verbatim, SHA-256
  `093149a928c07d238af402b5b25c56274bc2853858cd716574c699ef8c6c234b`; head
  `a3c5fa8b72e50939822f22364647dc844a3914a0`. Counts: **0 blockers, 1 major (#1), 3 minors
  (#2–#4), 210 notes (#5–#214).**
- **Review:** `review/gate03l-review.md`: all four findings true, severities kept. Minor 3 was
  understated: consumers already unfolded the definitions. Its §5 classifies the 210 notes, and its
  §6 lists six items the auditor missed (M1–M6 below; §6.1 would have been a major).
- **Rulings (user, 2026-11-05):**
  - **R-03l-1, option (B):** clean up the copies of `main`'s code in gate 03's repair PR, editing
    main-owned files on this branch.
  - **R-03l-2, option (A):** `StateLoop.orbit_zero` and `orbit_succ` keep `@[simp]`, on G3-6's
    terms.
  - **G3-5 (A)** for the duplicates.
- **Repair:**
  - **Major 1:** evidence only. `evidence-repairs/03l/axioms.log`, at
    `af91d53a414cdad6bbb61cecdc13f5e0e956d0b1`; the six files were unchanged since the audited
    head.
  - **Everything else:** PR [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203), gate 03
    clean-up part 1 (head `f29be161cd86cfc3a9c38bd203bfa095b4974086`, merged by
    `8ec28f130eaca5f7d7dc756953bde0807d41b7df`). Its evidence is
    `evidence-repairs/03l-cleanup1/`: the worker's report, the replay (134 modules), axioms (268),
    the seal with controls, lint before and after, and the statement diff, plus the maintainer's
    re-check of 11 key modules.
- Line numbers below are at the pin of round 2; Lean paths are under `TCSlib/Complexity/`.

| Finding | Severity (after review) | Resolution |
|---|---|---|
| 1 | major | **Fixed (evidence).** The full `#print axioms` of the six files' 90 public theorems and lemmas and of 16 consumers in `Randomized/Repetition.lean` and `Randomized/Primitives.lean` (106 distinct declarations): none depends on `sorryAx`, so none uses `main`'s five `Loop.lean` admissions. The staging tool now prints every public theorem of a pack's files (`--full`), and words an empty selection "not applicable", never "0 of 0" (`evidence-repairs/03l/gate03_stage.py.txt`). Round 2's attestation is generated that way. |
| 2 | minor | **Fixed** (#203, item G). A dated as-built erratum is appended to DESIGN §2.6 (`briefs/pass-shelat/DESIGN.md`, "As-built erratum (2026-11-05, gate 03l, minor 2…)"); the frozen text is unchanged. It records the new-output guard with the counterexample to the old one, the actual-pair invariant, the release-flag stop, the padding, the multi-module host (now H14), the two-state copier, the budget `A·(2n + 7 + P n)^D` and the `≤` counter test. §2.4 notes that `PairSplit` uses one work tape. `Repetition.lean`'s construction plan and the sketch of `polyTimeComputable_iterateFind` describe the built route (missed item M2). |
| 3 | minor | **Fixed** (#203, item E). 38 reading lemmas, none `@[simp]`, all `rfl` or `Iff.rfl` except `gstepBound_eval`. The review's 39th, `blk_eq`, is unnecessary because `BlockMapLoop.blk` is private, as recommended. The host's lemmas now sit in `TuringMachine/Build/ModuleHost.lean` (`clean_iff`, `state_eq`, `entry_eq`, `hostTM_k`, `hostTM_tm_q₀`, `hostTM_step_inl`); `copyTM_k`, `hostRet_*`, `hostCtrl_eq` and `hostTM_eq` are in `IterateFindHost.lean`. 18 unfolding sites are re-pointed: the review's 16, plus two in `polyTimeComputable_blockMap` that the seal found. The seal of 8 consumer files passes with controls (`evidence-repairs/03l-cleanup1/seal.log`). Check 8/8b is clean on the six files and the new host file (`lint-after.log`). |
| 4 | minor | **Fixed** (#203, item F). The 13 label docstrings now state their results ("The map `v ↦ …` (…) is polynomial-time computable"; `param_poly` adds that any first component works). `host_clean` (now `Turing.ModuleHost.host_clean`) states the bounded-call contract, and `Clean`'s docstring adds `0 < M.k` and the positive first halt (note 81). The optional `orbit_eq` wording is done. |
| 5–20, 22 | note | **No change** (general: source comparison, budget arithmetic, fresh coins, the `Loop.lean` dependency, inventory, the run-3 record, the adversarial instantiations, finite checks). Note 6's optional item, that `PairSplit` uses one work tape, is in DESIGN §2.4 (#203). |
| 21 | note | **Fixed** with #2. |
| 23–37, 39–53, 56–71, 73, 75–80, 82–83, 86–91, 93–97, 103 | note | **No change** to statements (private declarations that agree with their docstrings). Note 65 is fixed: `stepWord_verdictWord` no longer says "admissible". The copy rows (75–91, 103, 41–46) are resolved by M1. |
| 38, 54, 72, 74, 84, 85, 98, 104, 105, 107–111, 114, 120–122, 127–130, 135–139, 145–148, 156–164, 174–182, 186–196, 206–214 | note | **No change** (public declarations that agree with their docstrings). For 84, 85 and 104 the copies are resolved by M1. |
| 55, 81, 99–101, 125, 126, 131–134, 140–142, 149–152, 165–169, 183–185, 197–202 | note | **Fixed** with #3. Note 55 is `IterateFind.step_eq`, which bridges `IterateFind.step` to `guardedStep` (M4). Note 81 is `clean_iff` plus the docstring (#4). Notes 197–202 are `BlockMapLoop`'s lemmas, under the namespace renamed per M3. |
| 106, 143, 144, 153–155, 170–173, 203–205 | note | **Fixed** with #4. |
| 92, 102 | note | **Fixed** (#203). `copyTM` has `@[simps (config := { isSimp := false }) k]` (`copyTM_k`); the host machine has `simps k tm_q₀` (`ModuleHost.hostTM_k`, `hostTM_tm_q₀`). |
| 112, 113, 115–119 | note | **Scheduled:** clean-up part 2, DL-17. `StateLoop`'s `headBit_poly`, `tail_poly`, `isNil_poly`, `not_poly`, `or_poly`, `xor_poly` and `length_pairFstD_add_pairSndD_le` restate `main`'s lemmas, and about 23 files use them, some of which #195 changes. |
| 123, 124 | note | **Recorded** (R-03l-2): `orbit_zero` and `orbit_succ` keep `@[simp]` (`Randomized/Build/StateLoop.lean:186, 190`). |
| M1 | (review §6.1) unledgered duplication, a major until ruled | **(a) Fixed** (#203, DL-16): one public host `Turing.ModuleHost` (registry row H14, `machine-library-design.md` §14), consumed by `ClassNP/SAT.lean` and `IterateFindHost.lean`. Both copies are deleted, and SAT's public statements are unchanged. **(b) Fixed** (#203, DL-18): `UnaryMul` uses `PairSplit`'s parser (`Turing.PairParse`). **(c) Scheduled:** part 2 (DL-17). **(d) Recorded:** in row H14, `copyTM` is recorded as a parallel routine to `EmitIterBody`'s private copier, not a copy. |
| M2 | (review §6.2) `Repetition.lean`'s stale construction text (pack 03a's file) | **Fixed** with #2 (#203, item G). |
| M3 | (review §6.3) a latent clash between `StateLoop.BlockLoop` and `main`'s `Complexity.BlockLoop` | **Fixed** (#203, DL-19): renamed `StateLoop.BlockMapLoop`, with 17 declarations' statements kept. |
| M4 | (review §6.4) `IterateFind.step` restates `guardedStep` | **Fixed:** both definitions are kept, and `Repetition.lean`'s bridge goes through `IterateFind.step_eq` instead of `rfl`. |
| M5 | (review §6.5) the lint attestation used the presence-only lint | **Fixed:** #203's evidence runs `campaign_style_lint.py --check8b` before (5 WARN) and after (none on these files). Round 2's attestation records the same. |
| M6 | (review §6.6) two `@[simp]` attributes outside G3-6's list | **Recorded** (R-03l-2); see 123, 124. |

**Statement changes in the repair** (#203's `statements.md`):
- The host declarations moved to `Turing.ModuleHost` and were generalized: `Clean`, `clean_install`, `clean_emit`, `HostState` → `State`, `hostEntry` → `entry`, `host_call`, `guard_add`, `host_clean`. `host_call` and `host_clean` now exclude every control state, not only the anchor.
- `IterateFind.hostRet`'s type and `IterateFind.hostTM` (now an abbreviation) follow from the move.
- 17 declarations are renamed by M3.

No statement of `exists_pairSplitTM`, `exists_unaryMulTM`, `IterateFind.polyTimeComputable_find` or the `Repetition.lean` headlines changes.

**Found by the repair, for part 2:** five old `| zero => rfl` reads of `StateLoop.orbit` in files that part 2 edits (`QUEUE.md`), and ledger row DL-20: `Loop.lean`'s private `loop_first_halt` is the same lemma as `ModuleHost.first_halt`.
