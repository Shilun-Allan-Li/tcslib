# Review of the round-2 gate audit of PR #112 (the specification API)

**Verdict: the gate can close. PASS, 0 blockers, 0 majors, 0 minors, 1 note.**
- Every factual claim I could check cheaply holds.
- The note is true and non-blocking.
- What would resolve it now exists and passes:
  - an import-only consumer probe against `oleans-lapi2` (0 errors, 0 warnings, exit 0);
  - a re-run of the copy-route probe with a recorded exit status (0 errors, 0 warnings, exit 0).

  Add both to `audits/evidence/spec-api/r2/` if you want the stronger regression record.

## Inputs checked

- **Audit text:** `audits/spec-api-r2-findings.md` (untracked), read as data.
- **PR head:** `origin/lean/spec-api` = `caa93c124168f6f0678b47e38a0a0cb403fb7810`.
  - Its parents are `52965dc9` (round 2) and `db6ee4bd` (the campaign tip at merge time).
  - The six repaired files at `52965dc9` are blob-identical to my review's `edit/all` copies, i.e. the two patches applied unchanged.
  - `git diff db6ee4bd caa93c12 -- '*.lean'` lists exactly the seven API files (round 1's six plus `Build/Catalog`).
  - `git diff 52965dc9 caa93c12 -- '*.lean'` lists only `StepBlockForward` and `ZoneRebalance`, from #114 and #115.
- **Bundle:** `infra_local/gate-dispatches/31-spec-api-r2-gate/spec-api-r2-bundle.md`, SHA-256 `a82bd16a…710a`, as commissioned.
- **Evidence:** extracted from the campaign tip with `git archive` into `review/spec-api-r2-gate/ev/`.
- **Worktree:** `review/spec-api-r2-gate/wt-pr` (detached at `caa93c12`; clean after testing). Snapshot: `oleans-lapi2`.

## The audit's factual claims

| Claim | My check | Result |
|---|---|---|
| Bundle hash; 78 distinct sections, no duplicate paths | `shasum`; `^## ===== … =====$` headers | `a82bd16a…710a`; 78 headers, 0 duplicates; `BUNDLE-FILES.txt` has 78 entries |
| Both repair-patch hashes match the review | `cmp` against `review/spec-api-gate/repair-{required,optional}.patch` | byte-identical |
| Reversal reproduces round-1 blobs `47962f5`, `7e0ba25`, `e24fa1a`, `bd7d4ac`, `0b1c84c`, `c95ea67` | the patches' `index` lines against round 1's head (`28824c36`) | correct: WindowClock, CfgRecord, Contract/Basic, Contract/Catalog, Contract/Seam, RecordTable |
| 3 explicit theorems and 40 generated equations; `isSimp := false` throughout; no `@[simp]` | the patches | correct (15 required + 25 optional generated; `sweepMapWrite_apply` and the two endpoint-cell lemmas) |
| Probes match printed declarations: 30 Basic, 10 Seam, 3 Catalog | `#check` count in `r2/probes/*.lean.txt`; `@`-statements in `r2/logs/probe-*.out` | 30/30, 10/10, 3/3 |
| Explicit-lemma axioms | `r2/logs/probe-ApiCatalog.out` | `sweepMapWrite_apply`: none; the two cell lemmas: `[propext, Classical.choice, Quot.sound]` |
| Six repaired-file elaborations: exit 0, 0 errors; warnings Basic/Seam/Contract-Catalog/CfgRecord 0, RecordTable 4, WindowClock 1 | the r2 elaboration logs (my round-1 review's runs) | correct |
| Screen 712 → 714, 350 pair identities, 116,080 characters; one denominator 1,237 → 1,336 with 774 matched | `pairdiff` of `r2/logs/screen-required+optional.txt` against round 1's `screen-head.txt`; line diff | 0 new, 0 gone. The only changed line is `Seam.lean::ReturnContract.release reproduces Seam.lean::RoundContract.release: 774/1237 = 63%` → `774/1336 = 58%`, the attribute text appended to the release body. The r2 screen is byte-identical to my `screen-all.txt` |
| Lint check 8: 205 → 188 file/name pairs, 0 added, 17 removed; "the stacked comparison, not round 2 alone" | parsed `r2/logs/lint-{tip,head}-check8.txt` | exactly 205 → 188, 0 added, 17 removed. They are round 1's (`framedContract`, `seekPost`, `sweepPost`, the seven row contracts, `RecordAt`, `recordLength`) and round 2's (`ofSegment`, `returning`, `escaping`, `toRound`, `mapState`, `sweepMapWrite`); the auditor's qualifier is right |
| Replay: 85 distinct modules at `caa93c12`, all exit 0 / 0 errors, in the supplied order | `replay-lapi2.log` (== the evidence copy) | header `replay-lapi2 at caa93c12 … (85 modules)`, `# modules=85 failed=0`, 85 lines `exit=0 errors=0`. Order equals `r2/replay-order.txt`. The set equals my round-1 graph2 closure of the six repaired files. The script prechecks HEAD = `origin/lean/spec-api`, a clean tree, #115's replay, and 85 modules |
| Round 1: 89 modules at `28824c36`; the 4 omitted are Build/Catalog, NDHost, Scan, StepBlock | `replay-lapi.log` against round 2 | correct |
| Sorry counts equal on the 85 common modules except `StepBlockForward` 1 → 0 (#114) | joined the two logs | the only difference is `StepBlockForward sorry=1 → sorry=0` |

The auditor says it could not do two things: elaborate in Lean, and recompute the dependency
closure. I did both.
- The repaired files' elaborations are my round-1 review runs, and I re-elaborated today
  against `oleans-lapi2` (below).
- The 85-module set equals my own graph2 closure.
- I find no discrepancy in the audit's records section.

## The note (true; resolved, non-blocking)

**True.**
- `r2/probes/ApiBasic.lean.txt` and `ApiSeam.lean.txt` append the attributes and `#check`s.
  They prove the generated declarations exist and print their types, but they do not instantiate
  them in a consumer.
- `r2/logs/probe-ApiRunRoute.out` is 0 bytes. My original command echoed the exit status to the
  terminal, not into that file, so the file alone does not show exit 0.

**What resolves it** (done; files in `review/spec-api-r2-gate/`):
1. **Copy-route probe, re-run with its status.** `ApiRunRoute.lean.txt`, the r2 probe unchanged,
   imports only `Build.Contract.Catalog`. Against `oleans-lapi2` at `caa93c12`:
   `out/ApiRunRoute.out` records 0 errors, 0 warnings, `exit=0`.
2. **Consumer-instantiation probe** `ConsumerProbe.lean.txt`. It imports only
   `Build.Contract.Seam`, uses published lemmas only, and unfolds nothing. Against
   `oleans-lapi2`: `out/ConsumerProbe.out` records 0 errors, 0 warnings, `exit=0`. Its three
   examples cover the G4 routes:
   - **The round release, applied.** From `hp : R.pre i (d.mapState fun _ => anchor)`, it
     discharges `R.release.pre` by `RoundContract.release_pre` and takes the contract's own
     `run` field. With `release_time`/`release_post` it gets
     `(seamReleaseTM M anchor).runFrom d (R.time i (d.mapState …)) = (R.post i (d.mapState …)).mapState Sum.inr`.
   - **A returning round, released and sequenced.** `(Contract.seq C.release C₂ link hlink).time i d`
     equals the round's time at the anchor-mapped start, plus 1, plus `C₂`'s time at the
     released endpoint. It uses `Contract.seq_time`, `ReturnContract.release_time` and
     `ReturnContract.release_post`. The seq contract's state type is `(Unit ⊕ S) ⊕ S₂`, and the
     `Sum.inr` needs a type ascription; that is the only friction found.
   - **The index-free route.** `Round.iterate`'s segment passed whole to `Contract.ofSegment`,
     with `HeadBox` as the relation. `ofSegment_time`/`ofSegment_post` read the orbit's time
     `∑ r ∈ range n, τ (roundOrbit M τ c r)` and endpoint `roundOrbit M τ c n`. As the auditor
     says, neither `Round` nor `Segment` is unfolded; the round hypotheses stay as the
     consumer's obligations.

To record the resolution, copy both probe sources and their `.out` files into
`audits/evidence/spec-api/r2/` (or `r3/`). This changes no Lean and needs no new gate round.

## Can the gate close?

**Yes.** Round 2 has 0 blockers and 0 majors.
- The round-1 findings are closed: 1 and 2 by the repairs, 3 and 4 by the text, and 5 by
  `replay-lapi.log` and now `replay-lapi2.log`.
- The only new item is the note, resolved above.
- The merged head `caa93c12` is replayed (85/85, 0 failed).

Two items stay outside this gate, as the auditor says: the zone-layer API (#116) and G4's continuation.
