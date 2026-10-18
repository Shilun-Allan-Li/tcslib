# External audit pack — the step block's seam layout, round 2 (PR #124)

Campaign: the Arora-Barak chapters 3-4 plan. Round 1 of this statement gate
(`audits/seam-layout-statements-findings.md`, verbatim) returned **FAIL 0/2/1/7** on
`Turing.exists_seamLayoutTM` (`TuringMachine/Build/SeamLayout.lean`, sorried). The contract is
the one machine that redistributes a captured serialization
`pairEncode a ((List.replicate q true ++ [false]) ++ v)` onto the step block's table tape (`v`)
and summary tape (the unary word from cell `2`). The resolutions are in
`audits/seam-layout-statements-resolutions.md`; the maintainer's review is
`audits/evidence/c1/seam-layout/gate43-review.md`.

**The user's rulings (2026-10-18):**
- accept round 2's statement change (below);
- a standalone fill proves the contract after this gate;
- #125 and #126 were restacked below this PR.

**The head:** `lean/seam-layout` at `45b79f5f`, two commits on `5fd5dce8` (#126's content):
- the round-1 commit (unchanged);
- round 2: the review's patch `audits/evidence/c1/seam-layout/r2/r2-seamlayout.patch`, applied
  unchanged, with its docstrings and the facade entry reworded without campaign labels (the
  statement and the sketch's steps are the patch's).

| Round-1 finding | Repair in round 2 |
|---|---|
| 1 (major): the sketch did not compose the cited contracts | Eight phases joined by `phaseHostTM`: skip, skip back, the leaf `pairSkip`, the leaf `unarySplit`, a walk on `sm`, transfer, skip back, clear. Each names how the previous endpoint meets its row's `_run_ofCfg` hypothesis; each leaf says why no row serves. Exact time `T = 2n − r + 4h + 5q + 2|v| + 23 ≤ 18(n + 1)`. |
| 2 (major): `T` was chosen after the configuration, so it could depend on the input | `∀ a v q r, r ≤ |s| → ∃ T ≤ C·(|s| + 1), ∀ {z} d, … d.workTapePos src = r → …`. The start and end clauses are verbatim from round 1. Only the time's dependence is restricted. The round-1 form is a corollary. |
| 3 (minor): the probe never applied the contract | The round-2 probe applies it (below). |

## Brief for the auditor

1. **True.**
   - Is the round-2 contract achievable for one `C`, with `T` depending only on `a`, `v`, `q` and
     the source head's start `r`?
   - Check each of the eight phases against its cited contract and the previous phase's
     endpoint, and the two leaves' specifications.
   - Check the time formula, including `v = []`, `q = 0`, `a = []`, `r = 0` and `r = |s|`.
   - The review's simulation of the rows' own tables (`r2/sim_route.py`, `r2/sim-route.txt`;
     14,400 and 110,887 instances) is evidence, not a proof.
2. **Sufficient.** The round-2 probe (`r2/SeamLayoutConsumerR2.lean.txt`, with `r2/consumer-r2.out`)
   claims to derive:
   - the round-1 form, as a corollary;
   - the universal startup's (`UniversalK.exists_selfStartupTMK`) code-uniform first exit, with
     its tapes `k` and `k + 1`;
   - from R1′'s capture endpoint (`embedSilentRetTM_run`, `embedSilentCfg`): `Rep`'s table and
     summary fields for the initial configuration, through `FinTM.bufferTape_of_neg`, assembled
     by `Rep_iff`;
   - non-vacuity.

   Verify each against the consumers' statements.
3. **Not vacuous, not too strong.** Is the restriction on `T` satisfiable by the sketched route?
   Does it rule out anything a consumer needs?
4. **The docstrings** describe the statement and the route correctly, in public-facing terms.
5. **Records:** do the resolutions, this pack and the PR body agree with the evidence?

## Repository-side attestations (verify or challenge)

- **Elaboration** (against `oleans-lc1w`): 0 errors; 1 warning, the contract's `sorry`.
- **Consumer probe:** 0 errors; only the inline contract's `sorry` (`r2/consumer-r2.out`).
- **Freeze:** 1 → 1 public; "STATEMENT CHANGED: exists_seamLayoutTM" is the intended change.
- **Lint:** `TuringMachine/` 0 FAIL, 63 WARN, unchanged (`r2/lint-base.txt`, `r2/lint-r2.txt`).
- **Replay:** `replay-lseam2.sh`, 2 modules (the module and the `TuringMachine` facade), chained from
  `oleans-lx2b`. **Passed (user, 2026-10-18):** 2 of 2 at `45b79f5f`, 0 failed, static-equal (1).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/seam-layout-statements-r2-findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named
`seam-layout-statements-r2-findings.md`** (the findings table and the verdict line, no other
wrapping), and also paste its content in your reply.
