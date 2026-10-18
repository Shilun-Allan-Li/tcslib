# §13d G4's ruler: the lockstep walk and the seek, walk and scan contracts (statement unit)

**Why.**
- The G4 hosts-first survey (`audits/evidence/s13d/g4-hosts/G4-HOSTS-SURVEY.md`; obligation 3 of
  the G2–G4 statement gate) found every host the two G4 rows need already public, and one leaf
  missing: a two-tape lockstep walk that stays where it ends. That is the ruler for crossing to
  the mirror side and for slot offsets.
- It also found that the seek rows and `scanTM` have no Contract wrappers.
- **User (2026-10-15): public, gated first.** This unit is that statement phase. Its one theorem
  turned out short to prove, so the unit is complete: nothing is sorried. The gate audits
  statements and proofs together, before landing.

## What it adds

**`Build/Catalog.lean`** (R8.3, after `Turing.skipTM`):
- `Turing.walkTM k src moved dir`: while `src` reads a nonblank cell, every head in `moved`
  steps once in direction `dir`. At the first blank they step once more, into `done`. Nothing is
  written. It has the seek family's phases (`SeekPhase`).
- `Turing.skipTM_eq_walkTM`: `skipTM k i = walkTM k i (· = i) .pos`, by `rfl`. The two tables
  coincide.
- `Turing.walkTM_run_ofCfg`: the framed row.
  - From a word `w` read along `dir` from `src`'s head, delimited by a blank `|w|` cells along,
    the walk reaches `done` at exactly `|w| + 1`, never earlier.
  - Every moved head ends `|w| + 1` cells along; nothing else changes.
  - The trajectory is exact: at time `t` each moved head is `t` cells along, and every other head
    is fixed.
  - The cells under the other moved heads are never read.
  - Proof: the public `catalog_trace_run` over the family "every moved head `r` cells along".
- **`Turing.skipTM_run_ofCfg`, re-proved as the walk's one-tape rightward instance.** Its
  statement is byte-identical. The walk's proof generalizes the skip's old proof, so keeping both
  would duplicate it.

**`Build/Contract/Catalog.lean`:**
- `Turing.framedContract`: the contract of any framed one-exit row, from its framed theorem in
  the catalog's standard shape (touched heads within intervals, the others fixed).
- **`Turing.sweepContract` is redefined as its two-pass instance.** Its signature is identical;
  only the body keyword changes, from `where` to `:=`. The field proofs that both would carry
  are written once.
- `Turing.seekPost`: the seek family's endpoint (state `done`, the one head at a given position).
- Six instances:
  - `walkTM_contract` (moved heads between start and end, by the sign of `dir`);
  - `skipTM_contract`, `skipBackTM_contract`, `seekEndTM_contract`, `seekStartTM_contract`
    (one-line instances of the proved framed rows, with the endpoint `seekPost`);
  - `scanTM_contract`. Its exit set is every `done a`, so it is built directly.

## Checks (at #108's head `a9ee4701`, the G2 fill; against `oleans-lcanon4`)

| Check | Result |
|---|---|
| Elaboration | The two overlays concatenated into one probe (`tools/mkcombo.py`), because Contract/Catalog imports Catalog and no olean is written: 0 errors, 0 sorry warnings, and Catalog's 78 warnings unchanged (0 new). |
| Freeze | Catalog: +3 publics (`walkTM`, `skipTM_eq_walkTM`, `walkTM_run_ofCfg`); one authorized body change (`skipTM_run_ofCfg`); no private changed. Contract/Catalog: +8 publics; `sweepContract`'s body changed, its signature byte-identical (the freeze tool's heuristic flags the `where` → `:=` change; `logs/freeze-contract.log` ends with the exact comparison). |
| Axioms | All 119 publics of the two files use standard axioms only; 0 `sorryAx` (`logs/elab-combo-with-axioms.out`). |
| Regeneration | `scripts/mkwalk.py` on the two files at the merged tip `2e79d0f7` (Lean-identical to `a9ee4701`) reproduces both unit files byte for byte. |
| Lint | `campaign_style_lint.py` on `Build/`: 0 FAIL, the same WARN set. `style_lint.py` on the two files: 48 findings at base and head, none new. |
| Widths | No new line over 100 characters. |
| Copy-text screen v3 | Population: the two edited files, `Contract/Basic`, `Contract/Seam`, `Simulation`, `ZoneRebalance` and `CfgRecord` (`logs/screen-population.txt`). Base: 645 declarations, 392 pairs, 127,961 characters. Unit: 655, 390, 125,515. Gone: the three pairs against the skip's old proof (`skipBackTM_run_ofCfg` 68%, `seekEndTM_run_ofCfg` 60%, `seekStartTM_run_ofCfg` 58%). **New: one,** `seekStartTM_contract` ← `seekEndTM_contract` (207/390, 53%): mirror wrappers restating their rows' field-layout preconditions. The endpoint helper `seekPost` took it down from 58% (and the reverse direction under 50%). **Approved by the user (2026-10-15).** (`logs/screen-delta.log`) |
