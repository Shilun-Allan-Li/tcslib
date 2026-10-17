# Diagonal Part 1 statement gate: resolutions (round 1; gate CLOSED)

**Gate:** the in-place parameterization of Hydroxyi's `TimeHierarchy/Diagonal.lean` over a
diagonal simulator `DiagSimulator Φ` and a self-simulator `SelfSimulator Ψ`, with the four received
theorems re-derived as one-line instances (`audits/diagonal-p1-statements-pack.md`; bundle SHA-256
`8e4448c3f8e030876e2d5c56107af492dfbd0a7cb7f18f588d61617f1b8863c8`, 64 sections, dispatch folder
24; evidence `audits/evidence/diagonal-p1/`, committed in `fba93e7e`).

**Round 1** (`audits/diagonal-p1-statements-findings.md`, verbatim): **PASS, 0 blockers, 0 majors, 2
minors. The gate closes.** Both minors concern evidence checkers, not the Lean statements, and are
repaired in this closing commit (`workflow.md` §3).
- **Surface:** all ten received heads byte-identical; the six retained bodies and the header
  identical; the landed file rebuilt independently by `mklanded.py` and by the patch.
- **Definitions:** all 14 new declarations and the 8 generated constructors and projections
  reviewed; the timeout convention (accept on timeout, as received) is harmless.
- **Adversarial instances:** zero overhead, a non-halting `W`, a constant `decode` and `Ψ = 0` are
  each impossible; `T = 0` and the zero constants are harmless vacuity.
- **Fit for U2-U at k = 2:** the verdict-only clause, the `+1` and the padding quantifier order
  admit the planned instance; the `f log f` arithmetic from the probe gives the book form.
- **Consumers:** the five importers need no edit.
- **No duplication debt.** The received proofs were removed, not kept beside the generic ones.

The auditor did not run Lean. The elaboration, axiom and full-tree results stay maintainer
evidence (at base `cd450a52`, with a source-graph precheck at `c9cc485b`), and the fresh run and
replay at the actual landing tip remain landing obligations.

## Findings

| # | Severity | Finding | Resolution |
|---|---|---|---|
| m1 | minor | `names.py`'s whole-word screen excluded a preceding dot, so a fully qualified `def Complexity.TimeHierarchy.DiagSimulator := 0` passed | **Fixed.** The lookbehind no longer excludes the dot: a component counts alone or after a dot. Two new negative controls must fail and do: `names-qualified-decl` (that declaration) and `names-qualified-ref` (`@Complexity.TimeHierarchy.SelfSimulator.normalForm` in a proof). The old screen passes both (defect reproduced). `run.sh` now screens the base **and** the tip's whole tree (`git archive` of the tip; the tip's `Diagonal.lean` must equal the base's). Both pass: 723 files each, 0 occurrences, at `cd450a52` and `ff4cab18`. It runs again at the landing tip |
| m2 | minor | `copy-text-screen.py` (v1) skipped every pair with the same `(basename, short name)`, so the generic `DiagSimulator.time_hierarchy_of_pos` was never compared with a restored received `Complexity.time_hierarchy_of_pos` | **Fixed by the retrofit screen v3** (`audits/evidence/retrofit/copy-text-screen-v3.py`, SHA-256 `f4feac91…f181`). It identifies a declaration by path and source position and skips only the same declaration. A short name repeated in a file is labelled by its namespace-qualified name, with `#k` if still repeated. Where no file repeats a screened short name, the output is byte-identical to v2's. The auditor's mutation is the negative control `screen-restore`, and it fails as required. On the mutated tree v2 still reports 16 pairs (3,277 characters); v3 reports 18 (3,667), the new pair both ways: `DiagSimulator.time_hierarchy_of_pos` reproduces `Complexity.time_hierarchy_of_pos` at 86%, and the reverse at 83%. The control also checks that this exact pair is the one reported. Baseline, target and delta are regenerated with v3: before 16, after 16, new 0, gone 0; the pair lists equal the gate's v1 logs. Retrofit-wide: `audits/evidence/screenfix/v3/` |

**Negative controls: 9, all PASS** (`logs/negative-controls.log`), the six of the gate plus
`names-qualified-decl`, `names-qualified-ref` and `screen-restore`. `run.sh` requires all nine.

**What was re-run for this commit** (`scripts/closing-repair.sh`, read-only on the repository): the
names step on base and tip, the nine negative controls (one Lean elaboration, the cut control,
against `oleans-ltip3`), and the v3 screens with their delta. The other checks are unchanged
from the gate's run, and so are their logs and `logs/summary.log`. **`run.sh` runs in full, fresh,
at the landing tip**, with that tip's snapshot as its new third argument.

The bundle manifest named `BUNDLE-FILES.txt`, which was not in the bundle (the auditor checked the
section inventory directly). It is now committed with the evidence, so `SHA256SUMS` verifies.

## Rulings on the pack's questions (all as proposed)

1. **Field `W`:** kept (it follows `clockTM K W`).
2. **`diag_cost_le`:** kept, as the authorization requires. Any later retirement would be a
   separate compatibility decision.
3. **Verdict-only `SelfSimulator.simulates`:** kept. U2-U's full-output clause implies it, and it
   does not introduce the declined verdict-only universal row.
4. **The facade sentence:** unchanged in Part 1, because it is still true. It changes in the
   end-of-chain PR that lands `time_hierarchy_book`.

## Suggestions recorded for later (not gate conditions)

- **Compiled sanity checks:** `¬ Nonempty (DiagSimulator (fun _ _ => 0))`,
  `¬ Nonempty (SelfSimulator (fun _ => 0))`, no `SelfSimulator` with a constant `decode`, and
  machine-projection identities for `DiagSimulator.mono` and `SelfSimulator.toDiagSimulator`
  (`rfl`). These go to the end-of-chain PR, or to a small follow-up if wanted sooner
  (`backlog.md` RD-5).
- **`hΦ`:** sufficient but not minimal. Kept, as recommended.

## Landing

One PR applies `patches/Diagonal.patch` to `TCSlib/Complexity/TimeHierarchy/Diagonal.lean`. The
replay is the 11-module downstream closure (`replay-order.txt`, root excluded). Before the PR, the
full `run.sh` runs at the landing tip. MIG-1 S (open now) lands first. Diagonal then lands on the
post-S tip: `tipcheck.py`'s conditions, the name screen on that tip's tree, and the cut checks
against the S replay's snapshot.
