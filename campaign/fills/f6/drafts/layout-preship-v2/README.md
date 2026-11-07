# F6 last-ruler layout: bounded pre-ship components

**DRAFT — not ready to dispatch.** This is maintainer route evidence, not an F6
fill, target proof, gate, or acceptance of debt. No library source, admission,
import, public API, executable definition, Git state, shared snapshot or cache was
edited. `space_universal` remains admitted in the frozen source.

The concrete native startup component, last-tape layout, H5-to-return component,
bundle-reader consumer, zero-outer constructor typing, and one-cell correction
leaf all elaborated. The full prefix and its final run/cut/space premises have
**not** been constructed. This folder supplies bounded evidence toward the draft
route; it does not satisfy the standing requirement to pre-ship the entire route
before dispatch.

## Context and actual runs

The request supplied API worktree head
`1160c18f03fd318f0dec25738790935fa61379d4`, at
`/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/wt-natbits`.
The complete, read-only `oleans-mra2` snapshot was used directly for plain
elaboration. No Git command was run to independently attest that supplied head.
`context.json` records eleven source/compiled SHA-256 pairs captured before the
probes and checked unchanged afterward. `additional-context.json` records the
supplemental Catalog/StepBlock identities and toolchain/wrapper identity.

Every run used `devtools/seyoon/leanelab.sh`, sequentially, with local budget three
under the machine-wide limit five, no outer slot lock, and authorized scratch
access. Inputs were copied to unique `/private/tmp` directories. The request,
command, input/output hashes, exit status and raw stdout/stderr are retained for
**all 32 attempts**, including failed experiments and negative controls. No
compiled output was requested. `verification.json` independently checks receipts,
the retained copied inputs, final axiom sets, paired controls and unchanged pins.

Only `Hierarchy` is imported by each component. The implemented
`CodeTM.toFinTM_eq` is present in this context; the prerequisite merge is **not
attested here**. At assignment it was the unmerged #230/gate117 prerequisite.
The earlier draft's missing-reader assumption is therefore replaced by an actual
consumer in this folder, without claiming that dispatch prerequisites have merged.

## Final elaborated artifacts

| Input (all `.lean.txt`) | Checked result | Boundary |
| --- | --- | --- |
| `Final-native` | One fixed native startup plus stationary silent halt leaf; first halt exactly `Tα+2`, exact installed bank, silence through that time. | Does not build either physical header or bound this composite's space. |
| `Final-return` | Uniform H5 witnesses, then identity R1′ returning embedding at the same hosted time, with strict fresh-return cut and exact visited-set transport. | Physical suffix/ruler presentation and a source first halt are explicit hypotheses. |
| `Final-layout` | Exact whole-configuration equality for the first-three embedding into a `K+3` bank with ruler on physical tape `K+3`; also last index differs from `3` for `K>0`. | This is the required endpoint shape; no prefix is proved to reach it. |
| `Final-bundle` | Actual `CodeTM.toFinTM_eq` converts the target's bundled computation/space hypotheses to the raw coded machine. | Uses the implemented prerequisite, not a hypothetical reader premise. |
| `Final-zero-outer` | Full-bank configuration embedding is the identity; actual `startupLoopTM (k:=K+2) (K:=0)` has `K+4` tapes after explicit `Nat.zero_add` transport. | Constructor typing only; no run/space theorem or actual prefix premise is instantiated. |
| `Final-correction` | One fixed elementary leaf moves the last work head left once, from `ℓ+1` to `ℓ`, with a fresh live endpoint/cut. | It has not been seamed to the actual skip row. |

All six final inputs exit **0**, with **0 errors and 0 warnings**. Their eight
theorems have only subsets of `[propext, Classical.choice, Quot.sound]`; no
`sorryAx` occurs in a successful final artifact. Raw logs and exact per-declaration
axioms are retained rather than inferred from source inspection.

### Native startup and hosted return

`Final-native` obtains the actual witnesses of `exists_selfStartupTM c`
(`SelfUniversal.lean:87`). It fixes `A` before `α`, and fixes `Tα` before the
arbitrary suffix `w`. Its local leaf is one stationary, non-writing, non-emitting
halt step. The seam dispatch adds one step, so the first halt is `Tα+2`. Public
left/right seam equations prove liveness at every earlier time; public output
prefix monotonicity proves silence. The local initial-state override is transported
with `initCfg_eq_mapState` and `runFrom_with_q₀`, without reducing `seamCompTM`.

`Final-return` fixes H5's finite host, injection and positive coefficient **before**
all input/ruler/configuration/time parameters. It uses `exists_rulerHostTM`
(`InputDevice.lean:1226`) and `embedEmitRetTM_run` to turn an actual first halt into
the fresh live return `Sum.inr ()`. Its returning embedding is the identity on the
whole physical bank, adds no tape or step, and forwards exact output and visited
sets. H5's injected live-anchor cut is never assumed. The actual physical prefix
has not yet supplied the ruler presentation, source initialization or seam run
premises; these remain in `REMAINING.md`.

### Exact tape layout and correction

`Final-layout` uses `embedEmitCfg_forwardLoop_init`
(`UniversalParts.lean:182`) and public configuration fields. It checks a full
configuration equality, including state, input position, every tape function,
every head and output, rather than equality of tape counts. The H2-F three-tape
configuration is embedded through `Fin.castLEEmb` into the first three of `K+3`
bank tapes; the remaining `K` bank tapes are blank. H5 adds its ruler **last**, so
physical `N=K+4` and ruler index `K+3`.

The existing `suffixRulerCfg (k:=1) (K:=K)` definition
(`UniversalParts.lean:874`) puts its ruler at index `3`, before its scratch tapes.
The new equality is therefore the appropriate last-ruler reconstruction; the old
suffix layout is not silently substituted for arbitrary `K`.

The published `skipTM_run_ofCfg` (`Catalog.lean:12241`) takes `|w|+1` steps and
ends its selected head at `start+|w|+1`. For a ruler of length `ℓ` starting at
zero this is `ℓ+1`, as checked by its printed signature in
`Correction-interface.out`. `Final-correction` constructs the elementary local
leaf using `tapeAction last 0 none (-1) true`, then consumes the public
`step_of_tapeAction_move` equation. Its one-step endpoint preserves input position,
all tape contents, all other heads and output. It corrects the selected head to
`ℓ` and has a strict fresh-label cut. It copies no payload. The actual skip run,
its tape-window premise, correction dispatch and next scan remain unassembled.

## Rule 10 and controls

The final guard is before every theorem header and docstring. It seals **32**
ordinary TCSlib definitions, including model14/Simulation5, configuration maps,
seam/emitting/returning embeddings, ruler/forward-loop configurations,
`startupLoopTM`, the dependent coded bundle, the symbolic table/state encoders,
and `tapeAction`. Existing default simp attributes on `Action.apply`, `Cfg.init`
and `MultiTapeTM.initCfg` are removed locally. The earlier narrower guard29 runs
are retained, but the six authoritative final inputs use `final-guard.txt`.

`Final-controls-unsealed-v2` has **64 examples**, two for each sealed definition:
a pointwise delta equation and an abstracted function equation. It passes with
exit0/errors0. The otherwise identical `Final-controls-sealed-v2` has exit1 and
**exactly 64 expected `rfl` failures**, one in each example; there are no parser,
unknown-name or other error kinds. `controls-index.json` maps every definition to
its two source/error lines. The offline checker rejects synthetic missing,
duplicate-replacing-missing, exit0 and unexpected-kind logs.

Manual review of every final `rw`/`simp`/`unfold` argument found only published
equations/lemmas or local proof expressions. The local `physical`, `bank`, `ec`
and embedding lets are expanded in the layout proof; no sealed foreign
definition is named as an unfolding argument. The correction's `change` exposes
only a locally constructed record projection. Core/Mathlib reductions, including
`Fin` transports, are used under the standing allowance; their definitions are
not passed to rewriting/unfolding tactics. Structure projections and standard
abbreviations are not treated as ordinary-definition exceptions requiring new
reader APIs. This is scoped evidence for the recorded components, not an
exhaustive rule-10 certification of an unwritten F6 proof.

## Preserved unsuccessful attempts

The original inputs, requests, receipts and complete logs remain intact:

- `Native-startup-v1`: **4** raw diagnostics. Its original receipt counted 3
  because the first runner regex missed the coded `unknownIdentifier` diagnostic;
  the original counter is retained as `run-probe-original-counter.py.txt` and
  `verification.json` records the correction without changing that receipt.
  v2 had one remaining record-state goal; v3 passed.
- `Last-ruler-layout-v1`–v4 had respectively 4, 2, 2, 2 errors involving local
  record normalization, dependent `Fin.lastCases` motives, and rewriting both
  sides. v5 passed with four linter warnings; v6 and `Final-layout` pass cleanly.
- `Last-ruler-correction-v1`–v3 had one error each: record-update layout, an
  incorrect equation name, and an unexposed local record projection. v4 and the
  stronger final seal pass.
- The first expanded `Final-controls-unsealed`/`sealed` pair was invalid: its
  abstracted unary-state RHS binder inferred `ℕ` instead of `Fin n` (2/65 errors).
  The v2 pair adds the explicit binder type and is the authoritative 0/64 pair.
- `Additional-controls.lean.txt` is an unused generated fragment, never
  elaborated. `Interfaces` and `Correction-interface` are signature inspections,
  not route proofs. Any `sorryAx` printed after a failed attempt is diagnostic
  output from that failed attempt and is not included in a passing claim.

No further shared API is required by the six completed components. That does not
establish API sufficiency for the remaining full-prefix and loop assembly. See
`REMAINING.md`; no design leaf or debt was approved by this probe work.
