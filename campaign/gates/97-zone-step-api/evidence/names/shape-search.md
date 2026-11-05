# Gate 97: the statement-shape search over every ref (finding 6)

Run on 2026-11-05 by the cloud maintainer session, with `git grep -l -E <pattern> <ref> -- 'TCSlib/*.lean'`
over every remote branch head of the repository (339 refs: the campaign, `main`, every PR head
`pr/<n>`, every `lean/*`, `deliver/*` and `archive/*` branch). The shapes are the auditor's list
(finding 6) and the closing commit's new statements (`zoneRowPre_congr`,
`zoneRowPre_mapState_iff`). Candidate enumeration plus inspection, not an exhaustive search.
"N refs" counts the refs on which the file matches; the refs are named where there are six or
fewer.

### zero-time contract (ofSegment, precondition True, time 0): `ofSegment \(fun _ _ => True\) \(fun _ _ => 0\)`
- `TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean`: 2 refs (lean/zone-step-api pr/197)
- `TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean`: 72 refs
### the zero-length segment: `Segment\.zero`
- `TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean`: 98 refs
- `TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean`: 227 refs
- `TCSlib/Complexity/TuringMachine/Build/StepClock.lean`: 203 refs
- `TCSlib/Complexity/TuringMachine/Build/WindowRun.lean`: 209 refs
- `TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean`: 72 refs
### geometric sums or sums of 2 ^ idx: `geomSum|2 \^ idx`
- `TCSlib/Complexity/TuringMachine/Build/ZoneStep.lean`: 2 refs (lean/zone-step-api pr/197)
### compositions of exists_zoneRebalanceTM: `exists_zoneRebalanceTM`
- `TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean`: 189 refs
- `TCSlib/Complexity/TuringMachine/Build/ZoneStep.lean`: 2 refs (lean/zone-step-api pr/197)
### zoneRowPre under a change of state (one line): `zoneRowPre[^\n]*(mapState|bindState)|(mapState|bindState)[^\n]*zoneRowPre`
- `TCSlib/Complexity/TuringMachine/Build/ZoneStep.lean`: 2 refs (lean/zone-step-api pr/197)
### zoneRowPre unfolded with funext_iff (the inline invariance): `zoneRowPre, funext_iff`
- `TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean`: 118 refs

## Dispositions

- **Zero-time contracts.** `Contract.zero` (`Build/Contract/Basic`) exists only on #197's two
  refs. The other match is `ZoneRebalance`'s former private `zr_anchorContract` on the refs that
  predate #197, which #197 replaced by `Contract.zero`.
- **`Segment.zero`.** `Contract/Basic` defines it. In `CfgRecord` (2262, 2369, 4499 at the
  campaign tip), `StepClock` (648, 762) and `WindowRun` (802) it is the base case of an induction
  or the start of a run, not a zero-time contract. No other ref packages it as a contract.
- **Geometric and `2 ^ idx` sums:** only `Build/ZoneStep` (#197).
- **Compositions of `exists_zoneRebalanceTM`:** only `Build/ZoneStep`, beside the row's own home.
- **`zoneRowPre` under a change of state:** stated only in `Build/ZoneStep` (#197; the closing
  commit replaces its private copy by `zoneRowPre_mapState_iff`). `ZoneRebalance` proves it inline
  by unfolding its own definition with `funext_iff` (the twelve sites of finding 5), legal in the
  definition's home and recorded for re-pointing in the 12.2c window.
