# MIG-11a, the row contracts MIG-12 composes (PR #117): notes

## Why

The user scheduled the MIG items between the fills, starting with MIG-12 (2026-10-16). MIG-12
rebases `Build/CfgRecord` onto the contract layer (`audits/evidence/mig12/DESIGN.md`). That
rebase composes the framed rows `scanTM`, `skipTM`, `skipBackTM`, `clearTM`, `copyTM`,
`compareTM`, `incrementTM` (success) and `decrementTM` (success). The first four have contracts;
the other four did not. This is the part of MIG-11 that MIG-12 needs.

## What

The patch is `mig11a.patch`: one commit, `08bcc57d`, on the tip `c2ec34c5`. It is then stacked on
#116's round 2 (`b131d239`), so that the replays chain.

- **`Build/Catalog`:**
  - `compareStop u v`: the number of leading positions at which `u` and `v` hold the same symbol,
    `|takeWhile (·.1 = ·.2) (zip u v)|`. It comes with `compareStop_eq` (`rfl`),
    `compareStop_cons_cons`, `compareStop_spec` (below it both words hold the same symbol, at it
    they do not), `compareStop_unique` (the only such position) and `compareStop_le`
    (`≤ min |u| |v|`).
  - `compareTM_run_stop_ofCfg`: the framed compare at its exact time `2 · compareStop u v + 2`.
    The private stop of the existing trace equals `compareStop u v` by `compareStop_unique`, so
    the existing proof body moves here unchanged.
  - `compareTM_run_ofCfg` keeps its statement. Its proof is now the corollary
    `⟨compareStop u v, compareStop_le u v, compareTM_run_stop_ofCfg …⟩`.
  - Contracts need an exact time as a function of the index, and the old statement's time was
    existential; hence the new definition.
- **`Build/Contract/Catalog`:**
  - `copyTM_contract`: `sweepContract` at the touched heads `src` and `dst`, with the endpoint
    `sweepPost` writing `bufferTape w (q - pos)`. It comes with `copyTM_contract_frames`.
  - `compareTM_contract`: index `(u, v)`; time `2 · compareStop u v + 2`; endpoint the start with
    the verdict state; exits both verdicts (`Set.range fun b => some (done b)`, as for the scan).
    It is built directly, because `framedContract` has one fixed exit.
  - `simps!` and `simps` field equations for both.
- **`Build/Contract/Counter` (new):**
  - `counterRowContract`: the contract of a successful counter row from its framed theorem.
    Index `(w, v)` with `fix w = some v`; time `2 · |takeWhile lead w| + 2`; exits both
    verdicts.
  - `incrementTM_contract` (`incFixed`, `id`) and `decrementTM_contract` (`decFixed`, `not`) are
    its instances. The two were near-identical siblings, so they were factored at once
    (MIG-24's principle).
  - The module sits beside `Build/CounterLoop`, where the decrement is defined, so that
    `Contract/Catalog` does not import the counter loop.
  - Field equations: `simps` for the constructor, `simps!` for the instances.
- **`Build/Contract`** (the facade): imports and lists the new module.

## Checks (maintainer, against `oleans-lapi2`, the tip's snapshot)

- **Elaboration:**
  - `Build/Catalog` (`logs/elab-Catalog-{base,head}.out`): 0 errors, with 77 warnings at both
    base and head and no new warning (`warndiff`).
  - `Contract/Catalog` needs the new `Catalog` and so cannot be elaborated against the snapshot
    alone. It was elaborated as an overlay: the new `Catalog` and `Contract/Catalog` bodies under
    their merged imports, plus a probe (`logs/elab-ContractCatalog-overlay.out`). The result is
    0 errors, with 77 warnings, all `Catalog`'s. The replay elaborates both as modules.
  - `Contract/Counter` with a probe (`logs/elab-ContractCounter-probe.out`): 0 errors,
    0 warnings.
- **Generated names:** the 10 equations of copy and compare, and the 15 of the three counter
  contracts, resolve with their printed statements (the two probes).
- **Axioms** (the overlay probe): `compareStop_eq` none; `compareStop_cons_cons` and
  `compareStop_le` `[propext]`; the rest `[propext, Classical.choice, Quot.sound]`.
- **Freeze** (`logs/freeze.log`): publics added only (7 in `Catalog`, 3 in `Contract/Catalog`);
  the one authorized body change is `compareTM_run_ofCfg`.
- **Lint** (`logs/lint-head.txt`): 0 FAIL, 72 WARN over 79 files. The new file adds no WARN, and
  check 8 lists none of the new definitions.
  - **Corrected at the gate (minor 2):** that log was taken before the counter contracts were
    factored and before #116 merged. Re-run at `1358ff73` (`gate/lint-head-1358ff73.txt`): **0 FAIL,
    69 WARN over 79 files**, the tip's WARN set; `Contract/Counter` 131 lines, 3 public, no WARN.
- **The development probe:** `probes/StopScratch.lean.txt`, `compareStop`'s lemmas developed
  against the snapshot before insertion.
- **Screen** (`logs/screen-{base,head}.txt`, `logs/screen-delta.log`; the population is `Catalog`,
  `Contract/Basic`, `Contract/Catalog` and `CounterLoop`, plus `Contract/Counter` at the head):
  549 → 559 declarations, 320 → 321 pairs. No new copied proof:
  - `compareTM_run_stop_ofCfg` ← `compareTM_run` (50%) is the pre-existing pair of
    `compareTM_run_ofCfg`, moved with the body;
  - `transferMapTM_contract` ← `copyTM_contract` (54%, 76 characters) is the shared
    `sweepContract` call, the sweep-row contracts' constructor pattern.
- **Replay:** `replay-lm11a.sh`, the four modules' downstream closure at the stacked head
  (86 modules), from `oleans-lcapi`. **Passed (user, 2026-10-16):** 86 of 86, 0 failed
  (`replay-lm11a.log`).
  - The per-module sorry counts equal a static count (0 mismatches, 57 in total;
    `replay-lm11a-static.txt`).
  - On the 85 modules shared with #116's replay they are unchanged; the 86th is the new
    `Contract/Counter`.

## The statement gate (2026-10-16)

**PASS, 0 blockers, 0 majors, 2 minors: CLOSED.** Findings `audits/mig11a-statements-findings.md`
(verbatim); resolutions `audits/mig11a-statements-resolutions.md`; the review sub-agent's check
`gate/gate-review.md`.
- **Minor 1:** `counterRowContract`'s docstring claimed a width-preserving `fix`. Fixed in
  `98472df2`, docstring only (`gate/repair-docstring.patch`). `Contract/Counter` re-elaborated
  against `oleans-lm11a`: 0 errors, 0 warnings (`gate/elab-ContractCounter-docfix.out`).
- **Minor 2:** the stale lint log, corrected above.
- The replay at `b131d239` covers the head's Lean: no `.lean` file differs from `1358ff73`, and
  `98472df2` changes one docstring.
