# External audit pack: the zone step's API (PR #197, an API gate)

## Why this PR

G5 is the Hennie–Stearns simulation of `k` work tapes on two for binary machines
([AB09, §1.7]), `Turing.FinTM.two_work_tapes_run` in `Robustness/TwoTapes`, stated and sorried by
gate 92 (#189). Its zone layer has landed:
- the pure layer `Build/Zone`;
- the zoned carrier `Build/ZoneTape`;
- the rebalance and extension rows `Build/ZoneRebalance`, as `Turing.Contract`s with exact
  endpoints.

Gate 22 (the zone layer's statement gate) checked a fit probe, `campaign/items/s13d/g24/landing/parts/fit.tail`, that composes the
rows into one track's step and proves the amortized arithmetic. It carried two minors to G5:
- **minor 1:** `run_cost_le`'s step bound cannot absorb a fixed per-step cost at `k = 0`. Its
  proposed fix: carry an overhead `B`, add `B · T` to the conclusion, and do not fold it into a
  factor of `k`.
- **minor 2:** `trackStep_fit` omits `Fintype S` and the endpoint equalities for the input head,
  the output and the scratch head.

The user ruled **API first** (decision G5-F1, 2026-11-05;
`campaign/items/u2/G5-statements-plan.md` §6). The maintainer publishes the consumer side with
both minors met, by PR and this gate. G5's fill then writes only the controller, its invariant
and the count bound. The probe re-elaborates on the landed rows
(`campaign/items/u2/probes/G5FitLanded.lean.txt`).

**The PR:** #197 on `lean/zone-step-api`, head `0a1b64d59b707df679e66201496f2bced7197a98`, based on the campaign at `683e2adf571e8b6a5c62280d4a3739ec89687546`
(`evidence/patches/`, three commits, one per change). It changes `Build/Contract/Basic`, `Build/ZoneRebalance`
and the facade `TuringMachine.lean`, and adds `Build/ZoneStep`. Every file is the campaign's own.

## What changed (verify)

| File · declaration | Statement | Proof |
|---|---|---|
| `Build/Contract/Basic` · `Turing.Contract.zero` (+ `zero_pre`, `_time`, `_post`, `_lo`, `_hi`) | the zero-time contract of `M` at its own exit `e`: precondition `True`, time `0`, endpoint the start, envelope the start's heads | `Contract.ofSegment` of `Segment.zero`, the body of the private anchor it replaces; the five equations by `rfl` (written out, not `simps`, which does not see through `ofSegment`) |
| `Build/ZoneRebalance` · `zoneRowPre_iff`, `zoneRebalanceIndex_eq` | the two definitions' bodies | `Iff.rfl`, `rfl` |
| `Build/ZoneRebalance` · `zoneRebalanceIndex_le` | `zoneRebalanceIndex dir t D ≤ D.1` | `zoneShiftIndex_le` (`Build/Zone`) |
| `Build/ZoneRebalance` · the fields of `zoneRebalanceData`, `zoneExtendData`, `zoneRebalancePost`, `zoneExtendPost` (`zoneRebalancePost_state`, `_inputPos`, `_workTapes`, `_workTapePos`, `_output`, and the rest) | each field of each definition, fully applied | `simps` without the `simp` attribute |
| `Build/ZoneRebalance` · private `zr_anchorContract` | unchanged type; now `Contract.zero _ (some false) Unit x`, an `abbrev` | it unfolds to the same `ofSegment` term as before, so `zr_pinRe_ofSeg` still applies to it; six private proofs read `Contract.zero_*` where they read `Contract.ofSegment_*` |
| `Build/ZoneStep` (new) · `zoneTrackStepData` (+ `_of_lt`, `_of_not_lt`) | the data after one track's step: the rebalance if the scanned index is below `ℓ`, else the extension and then the rebalance | a definition; `if_pos`/`if_neg` |
| `Build/ZoneStep` · `exists_zoneTrackStepTM` | `∃ A, ∀ dir t, ∃ S (Fintype S) (DecidableEq S) M entry X, none ∉ X ∧ ∀ x, ∃ R : Contract M entry X (ZoneData k) x, R.pre = zoneRowPre ∧ ∀ D d, d.state = some entry → zoneRowPre D d → R.time D d ≤ A · (2 ^ zoneRebalanceIndex dir t D + 1) ∧ zoneRowPre (zoneTrackStepData dir t D) (R.post D d) ∧ (R.post D d).workTapePos 1 = d.workTapePos 1 ∧ (R.post D d).inputPos = d.inputPos ∧ (R.post D d).output = d.output` | `Contract.branch` on the rebalance's exits: `Contract.zero` on `done`; on `short`, `Contract.seq` of the extension and the rebalance. `A = 2C + C' + 2` from the rows' constants |
| `Build/ZoneStep` · `sum_two_pow_le_of_count` | `(∀ s < T, idx s ≤ L) → (∀ i < L, #{s < T \| i < idx s} ≤ T / 2^i + 1) → Σ_{s<T} 2^{idx s} ≤ (L + 1) · T + 2^L` | layer cake; Mathlib's `Nat.geomSum_eq`, `Nat.geomSum_lt` |
| `Build/ZoneStep` · `sum_cost_le_of_count` | `(∀ s < T, cost s ≤ B + A · Σ_t (2^{idx t s} + 1) + k) → (level and count hypotheses per track) → Σ_{s<T} cost s ≤ B · T + k · (A · ((L + 2) · T + 2^L) + T)` | `sum_two_pow_le_of_count` per track |
| `TuringMachine.lean` (facade) | imports `Build/ZoneStep`; one module-list entry | — |

**Names** (`evidence/names/`): none of the new names is used on any ref (the campaign, `main`,
every PR head). They include the `simps`-generated equations and `Contract.zero`'s.

## Brief for the auditor

1. **The statements.** Is each true as stated, at the right generality, and named and documented
   for public use?
   - **Minor 2.** Does `exists_zoneTrackStepTM` meet it? It exports `Fintype S` and the endpoint
     equalities for the scratch head, the input head and the output. With the precondition
     (tape `1` blank, the zoned head at home), these fix every field of the endpoint except the
     exit state.
     - The constant `A` is now uniform over directions and tracks; the probe chose it per
       `(dir, t)`. A consumer summing over tracks needs one constant.
     - The exit set `X` is exported abstractly, with `none ∉ X`, which is what the phase host
       (`Turing.Contract.inPhase`) needs. Is that the right form, or should the contract have a
       single exit?
     - The envelopes (`lo`, `hi`) are not exported. G5's bound is on time; is anything lost?
   - **Minor 1.** Does `sum_cost_le_of_count` meet it? At `k = 0`, `T = 1`, `cost 0 = B` the
     hypothesis holds and the conclusion is `B ≤ B`.
   - Is `Contract.zero` the right generic form? It is total (`pre = True`) and has the exit
     `{some e}`.
2. **The proofs.** Is `exists_zoneTrackStepTM` correct, in particular the time bound on the
   short path? There the rebalance scans to `ℓ` (`zoneRebalanceIndex_le` and the short exit),
   the extension costs `C' (2^ℓ + 1)` at the rebalanced data, whose level is `ℓ`
   (`zoneRebalanceData_fst`), and the retry scans to `ℓ` again
   (`zoneRebalanceIndex_extend_of_short`).
3. **Rule 10** (`evidence/rule10/`): `ZoneStep` is copied whole and sealed over the
   18 other-file definitions its proofs could reach, with `zoneTrackStepData` (its own)
   left open.
   - The copy elaborates with 0 diagnostics.
   - **The controls:** 36, a delta goal and an equation goal per sealed definition. Unsealed,
     all 36 close; sealed, none does.
   - Every `simp` call is `simp only`, with its lemmas listed; the one that discharged `none ∉ X`
     was a bare `simp`, replaced by the list `simp?` gave.

   Is any other-file definition unfolded or closed by reduction?
4. **Homes.**
   - `Contract.zero` sits beside `Contract.ofSegment` in `Contract/Basic`, the generic contract
     layer.
   - The equations sit beside their definitions.
   - `ZoneStep` is a new module above `ZoneRebalance` rather than an addition to it. Is that
     right? It keeps the 15k-line rows file unchanged apart from its equations, and only
     `Robustness/TwoTapes` and its consumers will import the new module.
5. **Duplication** (`evidence/screen/`, its `README.md`).
   - **The `ZoneStep` screen:** the v3 screen over 20 files (`population.txt`), restricted to
     pairs with a `ZoneStep` declaration on one side, as for gate 95. The module is new, so every
     such pair is new.
     - **At the first head:** one pair, `ZoneStep`'s private zero-time contract against
       `ZoneRebalance`'s private `zr_anchorContract` (99%). **Fixed** by the public
       `Contract.zero`, which both now use.
     - **At the final head:** no pair (1,991 declarations screened).
   - **The changed-files screen** (`changed-files/`): pairs with a declaration of any of the
     three changed Lean files on one side, over 22 files (adding the cited `Deterministic` and
     `Configuration`), at base and head. 562 pairs at base and 559 at head, **no new pair**. The
     three gone are inside `ZoneRebalance`, shortened by the anchor's re-point.

   Does anything else re-derive existing material, including inline steps?
   - `zs_rowPre_mapState` (the zone rows' precondition does not read the state) against
     `zoneRowPre_rebalancePost` and `zoneRowPre_extendPost`, which carry a `mapState`;
   - the arithmetic against Mathlib's geometric sums. The probe's private `2^n = 1 + Σ 2^i` was
     dropped for `Nat.geomSum_eq`.
6. **Public-facing text and lint** (`evidence/lint/`):
   - Campaign lint: 0 FAIL; `ZoneRebalance` loses one check-8 WARN, since `zoneExtendData` gains
     an equation.
   - The policy linter: 0 findings on `ZoneStep`; on the edited files, the base's findings and a
     line count.

## Repository-side attestations (verify or challenge)

- **Compilation** (`evidence/chain/`): every module was compiled with `lean -o`, in dependency
  order, into a copy-on-write clone of `oleans-lcf3` (the campaign after #190). That covers the
  five modules on the import paths from `Contract/Basic` to `ZoneStep` (`order.txt`). Every
  module exits 0 with no diagnostics.
- **Axioms** (`evidence/axioms/`): the new theorems are on `[propext, Classical.choice,
  Quot.sound]` or fewer.
- **Freeze** (`evidence/freeze/`): additive in public declarations.
  - `ZoneRebalance` gains three public source declarations. Its private changes are
    `zr_anchorContract`'s body and the six private proofs re-pointed to `Contract.zero_*`.
  - `Contract/Basic` gains `Contract.zero` and its five equations.
- **Replay:** `replay-lzsa` (`evidence/merged-tree/`), the downstream closure of the changed
  files, 111 modules, chained from `oleans-lcf3`. It passed: 111 modules, 0 failed. The static
  check found 0 mismatches, and the only `sorry`s are the campaign's existing 45 (`RecordTable` 4,
  `TQBF` 21, `RAMSimulation` 14, `Hierarchy` 4, `Savitch` 1, and `TwoTapes` 1, G5's own
  `two_work_tapes_run`).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/97-zone-step-api/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `zone-step-api-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
