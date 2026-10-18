# D7 split analysis — measured feasibility of the five file splits

Maintainer evidence for the D7 execution decision (2026-10-05). Tool:
`scripts/d7_split_analysis.py` (committed; full output at
`audits/evidence/d7-split-analysis-output.txt`). Method: parse each
file into top-level declaration blocks; extract every `private`
declaration; build the reference graph by comment-stripped,
word-boundary textual matching (comments and docstrings do not
constrain placement — Lean resolves no names there); union-find the
private families; a cut between blocks is **relocation-legal** iff no
private is defined on one side and referenced on the other.

Correctness cross-checks: per-file private counts reproduce the audited
inventories exactly (Loop 95, Primitives 167, Wrappers 20 pre-D6 — sum
282, the library gate's number; EXP 135, Nondeterminism 110, TMSAT 87 —
the epoch-2 gate's table); hub spot-checks confirmed in source (e.g.
`capturedSummary` defined near line 200 of `Nondeterminism.lean`,
referenced four times after line 1230); the cheapest balanced cut in
`Nondeterminism.lean` lands exactly at the forward/reverse semantic
boundary (`contSelect` opens the reverse assets).

## 1. Pure relocation is infeasible

The binding baseline (byte-identical relocation, dependent private
families kept together) admits **no useful split of any of the five
files**: each file's body is essentially a single private family.

| File | Body lines | Privates | Largest family span | Legal cuts (non-trivial) |
|---|---:|---:|---|---|
| Build/Loop.lean | 2,582 | 95 | blocks 5–102 ≈ 2,518 lines (98%) | none away from the edges |
| Build/Primitives.lean | 4,297 | 167 | blocks 1–182 ≈ 4,294 lines (99.9%) | none |
| ClassNP/EXP.lean | 2,834 | 135 | ≈ 2,775 lines (98%) | none |
| ClassNP/Nondeterminism.lean | 2,562 | 110 | ≈ 2,451 lines (96%) | tail only (the padding cluster, 106 lines) |
| ClassNP/TMSAT.lean | 1,816 | 87 | ≈ 1,786 lines (98%) | none |

This is a direct product of the exclusive-single-file fill discipline:
every batch chained its helpers (shared parser/scan vocabulary,
`catalogPrefix*`, the enum word vocabulary, `certificateSplit`,
`PolyControl`) across all its contract families.

## 2. Splitting requires cross-file visibility, quantified

Minimum number of privates that must become cross-file visible
(promotion to public, or to a reviewed internal namespace) for **any**
partition with every part ≤ 1,100 lines — a lower bound computed by
dynamic programming over all legal partitions, with unbounded part
count (a realistic 3–4-part split needs at least this many):

| File | Minimum promotions | Share of inventory |
|---|---:|---:|
| Build/Loop.lean | 34 of 95 | 36% |
| Build/Primitives.lean | 43 of 167 | 26% |
| ClassNP/EXP.lean | 24 of 135 | 18% |
| ClassNP/Nondeterminism.lean | 16 of 110 | 15% |
| ClassNP/TMSAT.lean | 8 of 87 | 9% |
| **Program total (lower bound)** | **≥ 125** | — |

Cheapest **balanced two-way** cut per file (both parts ≥ 800 lines),
with the hub inventory the cut would promote:

- `Loop.lean`: cost **29** at line 917 (801/1,781) — the whole
  `loopHost`/`loopBody`/`loopDebit` machinery bridges.
- `Primitives.lean`: cost **13** at line 2,912 (2,791/1,506; the large
  part still needs further cuts at further cost) — bridges include
  `catalogPolyUnaryTM`, `catalogPrefixTM`, `incFixedTM` + their
  contracts.
- `EXP.lean`: cost **15** at line 1,447 (1,394/1,440) — bridges include
  `enumLoop_run`, `enumWord`, the `enumCont_*` log/clean machinery.
- `Nondeterminism.lean`: cost **5** at line 1,230 (1,165/1,397) — the
  forward/reverse boundary; hubs are exactly the shared capture
  vocabulary: `acceptsWithin_iff_of_halts`, `captureEmission`,
  `captureEmission_correct`, `capturedSummary`, `capturedSummary_true`.
- `TMSAT.lean`: cost **13** at line 893 (801/1,015) — bridges include
  `polyUnaryTM`, `poly_unary_computes`, `polyTape`, the `tmsat*`
  request/answer vocabulary.

## 3. Why the splits are deferred behind E5

1. **The promotion sets intersect E5's work.** `polyUnaryTM`,
   `poly_unary_computes`, and `enumLoop_run` are live checkpoint routes
   that E5 may replace with catalog instances (the epoch-2 resolutions'
   binding inventory); `enumCarryTM`/`enumCaptureTM`/`choiceCopyTM`
   families are dead and will be deleted. Splitting first would promote
   helpers scheduled for replacement or deletion, and E5's deletions
   and replacements change both the family graph and the minimal
   promotion sets. Re-measurement after E5 is cheap
   (`scripts/d7_split_analysis.py`).
2. **The gate's discipline requires separate review of any
   visibility/interface change** (epoch-2 finding 12, adopted binding).
   At ≥ 125 promotions program-wide, this is an interface-engineering
   change to twice-audited surfaces, not the exceptional case the
   qualification contemplated. It should be submitted as **one**
   reviewed proposal — an internal-namespace policy (e.g.
   `…Build.Primitives.Internal`, names flagged non-API in docstrings)
   with the exact post-E5 name lists — for ride-along review in the
   next (E3) audit pack, then executed.
3. **Nothing forces a split now.** The auditor's own position
   (finding 12): the size exceptions impede review but create no
   missing premise or cycle, and nothing forces a split before the E3
   fills; the recorded lint justifications stand.

**Pilot candidate** for the post-E5 proposal: the `Nondeterminism.lean`
forward/reverse cut (cost 5, semantically exact); the five hubs are
genuinely contract-worthy shared vocabulary.
