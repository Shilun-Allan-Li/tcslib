# External audit pack: dedup NZ-1, "no machine halts in zero steps" (PR #217, a dedup gate)

## Why this PR

The dedup window (12.2c) started on 2026-11-06 (the user). It retires the ledger's families one PR
at a time. **NZ-1** (`campaign/duplication-ledger.md`) is one fact in two readings. A machine's
initial configuration is live, so no run halts within `0` steps.

- The **deterministic** reading is public as `Turing.FinTM.not_computesInTime_zero`
  (`TuringMachine/Finite`). Two proofs still re-derived it.
- The **nondeterministic** reading had no public lemma. It was proved five times, once in each of
  five files.

Gate 102's round 2, on #211 (G5's landing), raised both as majors: its finding 1 (the
deterministic sites) and its finding 2 (NZ-1's census). The user acknowledged NZ-1 on 2026-11-06:
publish and re-point now. This PR carries both fixes. #211's own file does not change; gate 102's
round 3 cites this gate.

**The PR:** #217 on `lean/dedup-nz1`, head `03052218` (full hash in the bundle header). It
consists of:
- `5e77e558`: the lemma, and the first three re-points;
- `2fdb84f7`: the docstring label fix, and the remaining four re-points from the by-kind search;
- a merge of the campaign, which brings in #208, #212 and #213. #216 merged after this head;
  see the replay attestation.

It changes 8 files: 43 lines added, 31 removed (`evidence/landing/nz1.diff`).

## What changed (verify)

**Published:** `Turing.NDTM.not_haltsWithin_zero (tm) (input) : ¬ tm.HaltsWithin input 0`, in
`TuringMachine/Nondeterministic`, beside `HaltsWithin.mono`, with a docstring and a sketch. Its
proof applies all-branch halting at budget `0` to the empty choice word, then rewrites with
`runWith_nil`, `initCfg_eq` and `Cfg.init_state`. The module's results list names it.

**Re-pointed (7 sites). No statement, definition or import changes.**

| # | Site | Old closing form | Now cites |
|---|---|---|---|
| 1 | `ClassNP/ExhaustiveReplay`: private `xr_not_haltsWithin_zero`, **deleted**; its use in `xr_first_depth` | `rw [runWith_nil, initCfg_eq, Cfg.init_state] at h0` | the NDTM lemma |
| 2 | `ClassNP/NDNormalForm` · `nf_forward`'s `hpos` | `rw [h00, take_zero, runWith_nil, initCfg_eq, Cfg.init_state]` | the NDTM lemma |
| 3 | `ClassNP/NTIME` · `NTIME_eq_empty_of_exists_zero` | definitional `hhalt [] rfl : some q₀ = none`, then `cases` | the NDTM lemma |
| 4 | `Randomized/ExpectedTime` · `AbortDecidesInTime.restart` | `hhalt [] …; simp [NDTM.initCfg, Cfg.init]` | the NDTM lemma |
| 5 | `Randomized/BPTIMEThreshold` · `BPDecidesInTimeWith.one_le` | definitional `.1 [] (by rw [hT]; rfl)`, then `simp` | the NDTM lemma |
| 6 | `TuringMachine/Build/Loop`: private `emCall_prepared_eval_first`'s `hpos` | `simp [ht0, runFrom_zero, initCfg, Cfg.init] at hh` | `FinTM.not_computesInTime_zero`, through `computesInTime_iff` with the actual output |
| 7 | `CircuitComplexity/Advice` · `DTIMEAdvice_eq_empty_of_eq_zero` (colleague-owned; a mechanical edit, which the user ruled allowed) | `simp [hT, MultiTapeTM.runFrom, MultiTapeTM.initCfg] at h` | `FinTM.not_computesInTime_zero`; its sketch names the lemma |

Sites 6 and 7 are gate 102 round 2's finding 1. Sites 3 and 4 are its finding 2's additions.
Site 5 was found by this PR's by-kind search.

**The search** was run at `1dd510aa`, by kind, and is recorded in the ledger's NZ-1 entry. It
covered:
- `rw`/`simp`/`change … at` with `runFrom_zero`, `runWith_nil`, `initCfg`, `Cfg.init` or
  `init_state`;
- zero-case scans (`by_contra`, `Nat.pos_of_ne_zero`, `eq_zero_or_pos`, `| zero`) near
  initial-configuration terms;
- `[] rfl` and `[] (by …)` instantiations of halting hypotheses;
- literal time-0 `runFrom`/`ComputesInTime`/`HaltsWithin`;
- `show`/`change`.

The sites already citing the deterministic lemma (`DTIME`, `TMSAT`, `CookLevin/Hardness`,
`EXPCOM`, and since #211 `TwoTapes`) need nothing.

**Classified as other facts, not members:**
- first-halt helpers from an arbitrary `cfg`: `Loop:219`, `Catalog:6463`, `SAT:3797`,
  `Hardness:6176`;
- runs from non-initial configurations that end in a state mismatch: `Hardness`,
  `NDCodeSimulator`, `NDNormalForm`, `StepBlockLoop`, `Contract/Basic`, `Contract/Seam` and
  `NTimeDiagonalizer`;
- composite runs at positive times: `UniversalK`, `NTimeHierarchy`, `Composition`, `Inclusions`;
- positive liveness facts (`state = some q₀`);
- other models: NARM's `narun`, `Yap`'s `badLang`, the oracle machines.

## Brief for the auditor

1. **The lemma:** is the statement right, is it well placed, and is it attributed and sketched
   adequately?
2. **Completeness:** does any proof in the library still re-derive either reading, in any closing
   form? Challenge the search and its exclusions.
3. **Scope:** is each re-point the old argument with the impossibility replaced by the citation,
   and nothing more?

## Repository-side attestations (verify or challenge)

- **Freeze** (`evidence/freeze/`, the head against the campaign's Lean `a28b8c42`):
  - `Nondeterministic`: 28 → 29 public, the one addition.
  - `ExhaustiveReplay`: 182 → 181 private (`xr_not_haltsWithin_zero` removed); the private
    `xr_first_depth`'s body changed.
  - `NDNormalForm`: the private `nf_forward`'s body changed.
  - `Loop`: the private `emCall_prepared_eval_first`'s body changed.
  - `NTIME`, `ExpectedTime`, `BPTIMEThreshold` and `Advice`: one authorized public body each.
  - No statement changes and nothing unauthorized.
- **Lint** (`evidence/lint/`, `git archive`s of both trees):
  - The campaign lint is identical at base and head: `TuringMachine` 0 FAIL / 71 WARN / 92
    files; `ClassNP` 0 / 18 / 21; `Randomized` 0 / 51 / 65; `CircuitComplexity` 0 / 76 / 104.
  - The policy linter over the 8 files gives 45 findings at both, the same findings with
    shifted line numbers: the existing sizes and sketch gaps of `ExhaustiveReplay` and
    `NDNormalForm`.
- **Replay** (`evidence/merged-tree/`):
  - `replay-lnz1` at `03052218` covers the downstream closure of the 8 files (261 modules,
    `Nondeterministic`'s and `Loop`'s), chained from the campaign snapshot `oleans-lcamp2`.
  - **261 modules, 0 failed.** The static check finds 0 mismatches.
  - The `sorry` warnings are all in the campaign's existing modules: `Loop`'s 5 (pre-existing,
    elsewhere in the file), `TwoTapes`' 1 (#211 closes it), `TQBF`'s 21, `Hierarchy`'s 4, and
    those in `Primitives`, `RecordTable`, `FormulaKit/Emit`, `RAMSimulation` and
    `GaussianSpace`.
  - #216 (RP-1) merged into the campaign after this replay. It changes 14 `SpaceComplexity`,
    `Randomized` and `ClassPSPACE` files, none of them in this PR. Before merge the maintainer
    re-runs the replay on the merged tree.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/108-nz1-dedup/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `nz1-dedup-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
