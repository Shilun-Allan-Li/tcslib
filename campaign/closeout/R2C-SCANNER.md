# R2c · The §12 common scanner: design note (draft for Seyoon, 2026-11-16)

Seyoon ruled R2c "do it" (2026-11-16). This note fixes the shape before any Lean, and lists the
new public API for approval (standing rule).

## 1. What is duplicated

`Build/Catalog`'s three sibling rows each carry their own copy of the same two-pass machinery:

| Row | Trace families and trace | Framed run(s) | Space wrapper |
|---|---|---|---|
| `clearTM` (`SweepPhase`) | `catalogClearF/R`, `catalog_clear_trace` (92 lines) | `clearTM_run_ofCfg` (32) | `clearTM_spaceUsedByTape` (36) |
| `incrementTM` (`FlagPhase`) | `catalogIncF/R`, `catalog_increment_trace` (137) | `catalog_increment_framed` (55), `_run_succ_` (44), `_run_overflow_` (40) | `incrementTM_spaceUsedByTape` (40) |
| `compareTM` (`FlagPhase`) | `catalog_compare_trace`, `catalog_compare_stop` (133) | `compareTM_run_stop_ofCfg` (51), `compareTM_run_ofCfg` (38) | `compareTM_spaceUsedByTape` (39) |

All three are "lockstep forward pass until a turn, return pass guided by one tape, enter `done`".
They already share `catalogTrace`/`catalog_trace_run`/`catalog_trace_clauses`; what is copied is
everything above that: the per-cell families, the trace inductions, the framed read-off and the
space wrappers (the ledger's 16 pairs, 5,520 characters, are mostly these). The existing
`scanTM` (Part 3) is not a fit: it always sweeps the whole word (no early turn), scans one tape,
and cannot write a blank.

## 2. Constraint: the frozen definitions stay byte-identical

`clearTM` has 103 uses in 16 files, `incrementTM` 64 in 9, `compareTM` 26 in 3; no consumer
outside Catalog unfolds their tables. Redefining them would change frozen definition bodies for
no gain. So **the three definitions are not touched**. Each is shown to agree, state by state,
with an instance of one generic scanner under an injective phase embedding, and its theorems
are transported with the existing `MultiTapeTM.runFrom_mapState_of_agreeOn`
(`TuringMachine/StateRenaming`). Every public statement stays as it is; only proofs change.

## 3. Proposed public API (in `Build/Catalog`)

- `Turing.LockScanPhase (V : Type)`: `fwd | bwd (v : V) | done (v : V)`.
- `Turing.lockScanTM (k) (lane : Fin k → Bool) (guide : Fin k)
  (fwdRule : (Fin k → Option Γ) → Option V × (Fin k → Option (Option Γ)))
  (bwdWrite : Fin k → Option (Option Γ)) : MultiTapeTM k Γ (LockScanPhase V)`: in `fwd`, apply
  `fwdRule` to the read column: write its writes, and either move the lanes right (`none`) or
  turn left into `bwd v` (`some v`); in `bwd v`, while the guide tape reads a symbol, write
  `bwdWrite` and move the lanes left; at the guide's left blank, step right into `done v`.
- `Turing.lockScanTM_run_ofCfg`: the framed run. Given the columns the lanes read at offsets
  `0..d` and the first offset `d` at which `fwdRule` turns, the machine is in `done v` exactly at
  `2d + 2` (no `done` earlier), with the forward writes and the return writes applied over
  `[pos, pos + d)`, every other cell, head, input position and output unchanged, and the heads'
  interval clause.
- `Turing.lockScanTM_spaceUsedByTape`: each lane visits at most `d + 2` cells, every other tape
  exactly its origin.

Instances (private, in Catalog): clear (`V = Unit`, one lane, `bwdWrite` blanks the lane),
increment (`V = Bool`, one lane, turn at the first `false` or the blank), compare (`V = Bool`,
lanes `fst`, `snd`, guide `fst`). Each row's existing public theorems become corollaries: the
transport lemma plus a read-off of the generic statement.

## 4. Size and process

New: the generic trace, framed run and space theorem, about 350–450 lines. Removed: the three
rows' families, traces, framed proofs and space proofs, about 650 lines. Net about −200 to −300
lines, and the 16-pair family collapses to one proof. One PR (gate 145), after R2a (gate 144),
since both edit Catalog; Catalog's downstream replay (about 130 modules).

## 5. Decision for Seyoon

Approve the API in §3 (names and the transport approach), or name changes. Not in scope:
`transferTM`/`copyTM` (already mapped-sweep instances) and `scanTM`.
