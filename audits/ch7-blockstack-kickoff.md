# Kickoff — ch7 block-stack audit (statement gate + fill verification)

Agreed at the PR #11 merge (plan decision log, 2026-10-10): the shared
block-query P-closure stack entered the campaign branch **unaudited** —
the ch7-phase1 gate (closed at `76fe2f46`, 0 blockers / 0 majors) covered
the 13-module statement surface including `CounterProgInput`,
`PolyTimePrefix`, and `PairEncode`, but everything after that gate has had
no external eyes. This round is owned by the ch7 campaign (Aparna) and
runs on the **merged ch3-4 branch tree**, under this repository's
`audits/TEMPLATE.md` (failure mode 5 — duplication debt — included).

## Pinned surface (the six post-gate commits `c4114867..d4503768`)

| File | Content | Lines |
|---|---|---|
| `TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean` | the bounded P-query loop; `polyTimeComputable_emitIter` | 500 |
| `TCSlib/Complexity/ClassNP/PolyTimeBlockTests.lean` | the three aggregated block tests | 653 |
| `TCSlib/Complexity/ClassNP/PolyTimeBlockMajority.lean` | the majority aggregator | 469 |
| `TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean` | safe-run combinators, output-prefix commutation, module-run embedding | 323 |
| `TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean` | the emit-iteration host (`exists_emitIterTM`, `C·(n+1)^c` budget) | 909 |
| `TCSlib/Complexity/ClassNP/PClosure.lean` (extension only) | one import + `mem_P_of_blockAny` / `mem_P_of_blockMajority` / `mem_P_of_blockXorAny` | +67 |

Also in scope as *fill verification only* (statements already gated at
ch7-phase1): the three discharged `PolyTimeModel` closures
(`closedUnderMajority` / `closedUnderAny` / `closedUnderShiftOr` — proof
bodies replaced sorries, statements untouched) and
`polyTimeComputable_xorD`.

## What the round must do

1. **Statement gate for the six files' public surface**: blind restatement
   of every public definition and theorem from its expression before
   reading docstrings; adversarial attention to the index-arithmetic and
   length quantifiers of the block decompositions (block width/count
   bounds, truncation at the last block, `n = 0` / empty-block corners) —
   this statement shape is where this repository's last two blockers
   lived.
2. **Fill verification on the merged tree**: sweep replay via
   `scripts/lean_check_tree.sh` (never `lake build`), independent axiom
   prints for the headliners and the discharged closures (at most
   `[propext, Classical.choice, Quot.sound]`, no `sorryAx`), lint on the
   touched directories.
3. **Duplication ledger line**: the stack's private `padAction`/`embedCfg`
   embedding machinery is design-parallel to the §12 `Build/Embed` layer
   (ledger watch item, `audits/duplication-ledger.md`); restate those
   privates blind and report any byte/near-copies of existing repository
   material. Harmonization itself is deferred to 12.2c — this round only
   establishes the facts.
4. Findings verbatim into `audits/ch7-blockstack-findings.md`; the gate
   closes on zero blockers and majors.

## Standing conditions until this gate closes

- **Consumption embargo**: no ch3-4 code cites `mem_P_of_block*` or the
  EmitIter hosts; no freeze claims on `PClosure.lean` (its extension rides
  this gate, Z1-rider precedent).
- **Rename window**: naming/placement of the shared primitive stays open
  until this round's pack is cut; after close, renames go through 12.2c.

## Disclosure (maintainer delta at merge)

Seven comment-only docstrings were added at merge time to satisfy the
campaign style linter (`resMatrix_apply`, `blockCount_le`,
`weakAdv_pos`/`_le_sixth`/`_ge`, `measurable_coordIndicator`,
`integrable_coordIndicator`) — no statement or proof changed; audit them
as maintainer text, not author text. `Randomized/Classes.lean` > 1000
lines is justified in the plan decision log (split belongs to the ch7
campaign). The merge-time verification sweep (48 modules, the ch7 closure
+ facades) passed with exactly one `sorry` warning —
`Expanders/Chernoff.lean` (Theorem 7.41, the intentional statement-only
stub).
