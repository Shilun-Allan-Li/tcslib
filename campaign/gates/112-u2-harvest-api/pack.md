# External audit pack: the U2 harvest API, `Build/UniversalParts` (PR #221, an API gate)

## Why this PR

F6 (`space_universal`, `SpaceComplexity/Hierarchy`, [AB09, Exercise 4.1]) composes its route
from pieces of the self-universal machine U2-E/U2-U (`TuringMachine/UniversalK`): header scans
with a ruler, the startup-to-loop seam, the forwarding loop's lockstep readings, and the
suffix-ruler layout. Those pieces were privates of `UniversalK`, and rule 11 forbids citing
another file's privates. This PR publishes them. It follows gate 20 (the H1 harvest) and gate 73
(U2's API).

**The user's rulings (2026-11-06):**
- the rows go in a **new `Build/` module**, not in place in `UniversalK`;
- the harvest comes before RO-1's `UniversalK` edits;
- **RS-1**: the restart identity is published here.

The plan is `campaign/items/roadmap3/PLAN.md`, §F6 (c), and the design note is
`evidence/probes/DESIGN.md`.

**The PR:** #221 on `lean/u2-harvest-api`, head `51843dd2` (full hash in the bundle header). It
consists of `065e1e80` (the new module and its facade entry), `db12c154` (`UniversalK` cites it
and the 26 harvested privates are deleted), and merges of the campaign, the last after #218 and
#219. Diff:
- `Build/UniversalParts.lean`: +976 (new);
- `UniversalK.lean`: +44 −790, from 2,873 to 2,127 lines;
- the `TuringMachine` facade: +6.

## What changed (verify)

**`Build/UniversalParts`** (namespace `Turing`; the forwarding-loop rows under
`Turing.StepBlock`; private prefix `up_`). It imports `Build/StepBlockForward`,
`Build/InputDevice`, `Build/Rewind` and `Mathlib.Algebra.Group.Action.Defs` (for `smul_eq_mul`),
none of which reaches `UniversalK`. It has 22 public rows:

| Group | Rows | Source private |
|---|---|---|
| restart identity (RS-1) | `MultiTapeTM.initCfg_eq_mapState` | `uk_init_mapState` |
| forwarding loop at its start | `StepBlock.forwardLoopCfg_init_workTapes`, `_init_fields`, `_halt_iff`; `embedEmitCfg_forwardLoop_init` | `uk_encode_init_tapes`, `uk_encode_init_fields`, `uk_encode_halt`, `uk_embed_init` |
| lockstep readings | `StepBlock.forwardLoop_forward`, `_live`, `_converse` | `uk_loop_forward`, `uk_loop_live`, `uk_loop_converse` |
| seam | `startupLoopTM` (def), `_initCfg`, `_live_of_le`, `_runFrom` | `uk_loopTM`, `uk_loop_init`, `uk_loop_pre_live`, `uk_loop_run` |
| seam space | `startupLoopTM_spaceUsed_le`, **generalized** to any seam endpoint (the hypotheses of `startupLoopTM_runFrom`) | `uk_loop_space` (fixed native endpoint) |
| header scan | `headerScanTM`, `headerScanCfg` (defs; `simps` field equations), `headerScanTM_run`, `headerRulerTM`, `headerRulerTM_run` | `uk_scanTM`, `uk_scanCfg`, `uk_scan_run`, `uk_headerTM`, `uk_header_run` |
| ruler | `headerScanCfg_ruler`, **generalized** from a blank tape to a ruler prefix `true^m` (`m = 0` is the old statement), so two scans compose | `uk_scan_ruler` |
| suffix-ruler layout | `suffixRulerCfg` (def; `simps` field equations), `rulerHostCfg_fields`, `suffixRulerCfg_embed` | `uk_suffixCfg`, `uk_ruler_fields`, `uk_embed_suffix` |

Moved with them, renamed: `up_scan_zero`, `up_scan_step`, `up_scan_pair`, `up_scan_header`. A
private corollary `up_scan_ruler_blank` restates the `m = 0` case, derived from the general form.
After renaming, 23 of the 26 moved declarations are textually identical. The three that differ
are the two generalizations and `headerRulerTM_run`, which cites `up_scan_ruler_blank`.

**`UniversalK`:**
- `exists_selfUniversalK` and `universalK` keep **byte-identical statements**; only their bodies
  are re-pointed.
- The private `uk_suffixStartupTM`/`_run` are re-pointed.
- Three definitional reads of the now-foreign `suffixRulerCfg` are fixed through its field
  equations: in `uk_suffixStartup_run`'s final step, in a `rfl` for its state in `universalK`'s
  body, and in `universalK`'s live-prefix step. The seal found the second and third.

## Known deviations (for the audit)

- **Size:** `UniversalParts` has 976 lines, above the 600-line target and below 1,000 (campaign
  lint INFO). Its four groups cite one another.
- **RS-1's home:** the restart identity is a `MultiTapeTM` fact published in a `Build/` module
  rather than `TuringMachine/Finite`. That is the user's ruling, which avoids a replay of most of
  the tree. RS-1's other sites re-point to it in the dedup window.
- **`headerRulerTM_run`** still needs a blank ruler tape. F6's second header composes
  `headerScanTM_run`, `headerScanCfg_ruler` and `rewindTM_run_ofCfg` instead.

## Brief for the auditor

1. **The API:** are the rows correctly stated and placed? Are both generalizations right, and do
   they reduce to the old statements? Is anything missing that F6's route needs? The consumer
   probe below composes the route.
2. **Rule 10 / rule 11:**
   - Does `UniversalParts` read other files' definitions only through published equations?
   - Does `UniversalK` now read `UniversalParts`' definitions only through their equations?
   - Is nothing private cited across files?
3. **The move:** is it faithful, with no statement or behaviour change beyond the two
   generalizations? Are `UniversalK`'s public statements unchanged?
4. **Public text:** docstrings, attributions and sketches.

## Repository-side attestations (verify or challenge)

- **Freeze** (`evidence/freeze/`, `UniversalK` at the head against the campaign `7027dead`):
  - 12 → 12 public, with no statement change;
  - the only body changes are the two authorized ones, `exists_selfUniversalK` and `universalK`;
  - 67 → 41 private: 26 removed, as listed above, and 2 changed (`uk_suffixStartupTM`,
    `uk_suffixStartup_run`).
- **Rule 10** (`evidence/probes/Seal*.lean.txt`, `.out`):
  - `UniversalParts` is sealed with the 16 other-file definitions it reads made irreducible
    (`SealParts`). The body elaborates; the 16 controls fail sealed (16 errors, all on the
    control lines at the end) and close unsealed (`SealParts0`, 0 errors).
  - `UniversalK` is sealed with the 5 moved definitions irreducible (`SealUK`). The body
    elaborates; the 5 controls fail sealed and close unsealed (`SealUK0`).
- **Axioms** (`evidence/probes/Ax.*`): all 22 rows, their 10 generated field equations,
  `universalK` and `exists_selfUniversalK` (28 prints) use only the standard three or fewer. No
  `sorryAx`.
- **Consumer probe** (`evidence/probes/Probe.lean.txt`, `probe.out`, exit 0):
  - two header scans compose to `true^(ℓ₁ + ℓ₂)`;
  - the startup runs under the ruler host on the first header's suffix (`rulerHostCfg_fields`),
    within `B + ℓ₁ + 2` cells;
  - the final seam is closed with `startupLoopTM_runFrom` and `startupLoopTM_spaceUsed_le`
    through `suffixRulerCfg_embed`;
  - F6's layout is `pairEncode (bits s) (pairEncode α x)`.

  Only F6's own leaves are `sorry`, in `route_space`.
- **Screen** (`evidence/screen/`; `UniversalK`, `StepBlockForward`, `InputDevice`, `Rewind`,
  `SelfUniversal`, and at the head `UniversalParts`): the base has 134 declarations and 23 pairs,
  the head 137 and 23. 5 pairs are new and 5 gone, and the new ones are the gone ones renamed,
  moved with their declarations (`pairdiff.txt`). No new copy.
- **Lint** (`evidence/lint/`):
  - The campaign lint on `TuringMachine` gives 0 FAIL, 72 WARN, over 92 files at the base and 93
    at the head; `UniversalParts` adds only INFO lines (its size).
  - The policy linter gives 1 finding at both, `UniversalK`'s size (2,873 → 2,127 lines, still
    above 1,000).
- **Replay** (`evidence/merged-tree/`): `replay-lhv2` at `51843dd2` covers the downstream closure
  (7 modules: `UniversalParts`, `UniversalK`, `SelfUniversal`, `Hierarchy`, `UniversalTlogT` and
  both facades), chained from the campaign snapshot after #218 and #219. **7 modules, 0 failed.**
  The static check finds 0 mismatches. The 2 `sorry` warnings are `Hierarchy`'s F6 and E-PAD.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/112-u2-harvest-api/findings.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `u2-harvest-api-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
