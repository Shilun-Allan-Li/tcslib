# R2c · The §12 common scanner: design note (2026-11-16)

**Approved (Seyoon, 2026-11-16): the API of §3 and the transport approach, as written.**

**Outcome (2026-11-16): built, measured, and carried (Seyoon).** See §6.

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

## 6. Outcome: built, measured, carried

The design was built in full (`archive/R2c-LockScan.lean.txt`, then spliced into Catalog on top of
R2a: `archive/R2c-Catalog-splice.diff.txt`). It works: `clearTM_run_ofCfg`,
`catalog_increment_framed` and `compareTM_run_stop_ofCfg` are re-derived through `lockScanTM` with
their statements unchanged, the three space wrappers follow, and Catalog compiles. But it does not
pay off:

| | Catalog lines | Copy-screen pairs (Catalog alone) |
|---|---|---|
| R2a head | 4,282 | 48 |
| with R2c | 4,643 (+361) | 58 (19 new, 9 gone) |

The new scaffolding (per-row configuration lifts, run transports, space wrappers) resembles itself
(`archive/R2c-pairdiff.txt`). Further factoring was estimated at +150–200 lines at about the base
pair count, still net growth. §4's estimate (−200 to −300) was wrong: it counted the removed rows'
traces but not the transport and instance code each row needs.

**Ruled (Seyoon, 2026-11-16): carry the family** (12.2c item 5, the §12 sibling rows) in the
register, as measured debt: unifying costs more code than it removes. The archive is the starting
point if a future change makes a generic scanner worthwhile (for example, a fourth sibling row).
