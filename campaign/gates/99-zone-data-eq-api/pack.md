# External audit pack: the zone data maps as whole values (PR #207, an API gate)

## Why this PR

G5 is the Hennie–Stearns simulation, `Turing.FinTM.two_work_tapes_run` in
`Robustness/TwoTapes`. Its fill reads the zone layer only through published equations (rule 10),
which a seal test checks by making every other file's definition irreducible. A review of G5's
draft brief (`evidence/review/`, the brief's `review/REVIEW.md` finding B1) found that it cannot
read a track's contents after a track step:

- `ZoneData k` is `Σ ℓ, Fin k → ZoneContents ℓ`.
- The `simps` fields `zoneRebalanceData_snd` and `zoneExtendData_snd` state the data maps
  pointwise. The left side sits at the map's own level, `(zoneRebalanceData dir t D).1`, the right
  side at `D.1` (or `D.1 + 1`). The two agree only by unfolding the map.
- Under the seal, a rewrite with them leaves goals that print as `f x = f x` but differ in a
  hidden implicit level: `rfl` cannot close them, `zoneTrackTape_extend` does not match, and the
  Σ-level equation cannot be rebuilt from the fields (`evidence/review/G5RvSigma2.out`, S1–S5).

The user ruled **publish, by a new API PR** (2026-11-06).

**The PR:** #207 on `lean/zone-data-eq`, head `f866f31438630016f8c733dcc452345eddda6b27`:
`dbad3b06478ac46ed49f1346f8444d265360a7e8` (`evidence/patches/`), then a records-only merge of the
campaign. It changes one file, `Build/ZoneRebalance`.

## What changed (verify)

| Declaration | Statement | Proof |
|---|---|---|
| `Turing.zoneRebalanceData_eq` | `zoneRebalanceData dir t D = ⟨D.1, Function.update D.2 t (zoneRebalance dir (D.2 t))⟩` | `rfl` |
| `Turing.zoneExtendData_eq` | `zoneExtendData D = ⟨D.1 + 1, fun t => (D.2 t).extend⟩` | `rfl` |
| the module docstring | the equations paragraph and the main-results list name both | — |

Both sit after the `simps` attribute that generates the pointwise fields, and say when to use
which. No statement changes (`evidence/freeze/`: public 23 → 25, private 852 → 852, nothing else
changed).

## Brief for the auditor

1. **The statements:** true, at the right generality, and named and documented for public use?
   Are they the right fix for the hidden-level problem, or should the pointwise `_snd` fields be
   stated differently as well?
2. **Sufficiency:** does the consumer probe (`evidence/rule10/ZDEConsumer`) show that a sealed
   consumer can now reach the contents: the rebalanced track, another track, the extension, and
   the represented tape's move through `zoneTrackTape_rebalance_right`?
3. **The home:** beside the data maps and their fields in `Build/ZoneRebalance`.

## Repository-side attestations (verify or challenge)

- **The consumer probe** (`evidence/rule10/ZDEConsumer.lean.txt`, on `oleans-lzde`): the review's
  failing sealed proofs re-done with the two equations, under the review's seal of eight
  definitions (`zoneRebalanceData`, `zoneExtendData`, `zoneTrackStepData`, `zoneRebalanceIndex`,
  `zoneTrackTape`, `zoneRebalance`, `zoneShiftIndex`, `ZoneContents.extend`): **0 diagnostics**,
  exit 0.
- **Controls** (`ZDECtl_unsealed`/`_sealed`): `#ctl_rfl` and `#ctl_eqn` for each of the eight:
  16 pass unsealed, 16 fail sealed.
- **Axioms** (in `ZDEConsumer.out`): `zoneRebalanceData_eq` on `[propext, Quot.sound]`,
  `zoneExtendData_eq` on `[propext, Classical.choice, Quot.sound]`.
- **Names** (`evidence/names/`): neither name is used on any of 362 refs except #207's branch.
- **Screen** (`evidence/screen/`): by v3's own extraction (`decl-list.py`), both new bodies are
  3 characters, under the screen's 60-character cut-off, and every other declaration of the file
  has the same extracted body at base and head. The screen is therefore unchanged by
  construction; no run is attested.
- **Lint** (`evidence/lint/`): the campaign lint on `TuringMachine` 0 FAIL, 71 WARN over 92 files
  at base and head, the only change `ZoneRebalance`'s size line (15,402 → 15,414); the policy
  linter the same 26 findings at base and head, the size line moving.
- **Replay** (`evidence/merged-tree/`): `replay-lzde` at `f866f314`, the downstream closure of
  `ZoneRebalance` (5 modules), chained from `oleans-ldwa3`: **5 modules, 0 failed**; static 0
  mismatches; the one `sorry` is `TwoTapes`' `two_work_tapes_run`, G5's target.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/99-zone-data-eq-api/findings.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as `zone-data-eq-api-findings.md`** (the findings table and the verdict
line, no other wrapping): push it to `arora-barak-ch3-4/inbox/` on the branch
`exchange/pass-shelat-ch5-8` (`git pull --rebase` first, add only that file, never force-push, no
PR), and also paste its content in your reply.
