# io-sprg Phase A — M2 checkpoint addendum

M2 stretch proofs and local checks are complete at source
`4ecc40c04a001bc87349b7ec368ece309774c28a`; M2 packaging and publication remain
pending. This addendum updates the published M1 report rather than replacing its
historical evidence. M1 was published at exchange commit
`10da7fdefd9a44023cc117a672f19e8a3617b81d`, from source
`19dde91afc384656e7e47cb018057e088d4ded0a`.

All four original M2 bodies are filled, with three new theorem-only helpers.
The cumulative record is **110 CHECKED_PASS steps: 104 original bodies and six
new helpers**, leaving **42 original direct proof holes**. M3–M6 remain unfinished,
T1–T6 remain unproved Phase B targets, and the complete end-to-end proof gate is open.

## Scope and proof route

| M2 original obligation | Saved checked step | Current source anchor |
| --- | --- | --- |
| `Params.seedBitsAt_le` | 104, repaired | `Stretch.lean:82` |
| `jls_seedBits_eq` | 105 | `Stretch.lean:390` |
| `jls_seedBits_le` | 106 | `Stretch.lean:404` |
| `jls_hasPolyStretch` | 110, repaired | `Stretch.lean:428` |

The new owned `Internal` helpers are `w_lower` (step107, line204),
`stretch_gaps` (step108, line223), and `eventually_seed_relative_gap`
(step109, repaired, line254). Failed attempts and their repaired check records
remain under `evidence/steps/` and `evidence/build/M2/`; only the final recorded
CHECKED_PASS states are counted above.

The seed bound uses the explicit witness `C = 2*(2^P.D)+12`, including zero and
rounding cases, for
`seedBitsAt κ ≤ C*(κ+1)^5*(n κ + m κ / w κ + 1)`.
The width helper proves `κ^(E*δ/2)/2 ≤ w κ` for `κ≥1`.
The sufficient E0 threshold supplies positive public/noise exponent gaps; the
relative-gap helper then proves `seedBitsAt κ ≤ m κ * κ^(-ε)` eventually.
Rational δ remains construction data and is coerced to real values for analysis,
as required by SP-W1. These payload bounds do not depend on the public prime.

The final proof retains the actual coefficient from the public
`Complexity.PolyExpr.eval_le` output-polynomial bound. It uses
`D = max 1 ((C:ℝ)*2^c)` and `η = ε/(2*(c+1))`, and absorbs the fixed
`D^η` factor using the existing real-power growth API. The discarded generic
monic-normalization route (`StretchFinal` candidates02/06) is not the implemented
proof route and must not be described as approved reuse or completed source.
No new algorithm, machine, sampler, efficiency claim, or frozen statement is
introduced by these three helpers. The helper plan is
`evidence/checkpoints/M2/helper-plan.md`.

SP-W3's seed-growth conjunct is proved together with the power bound. The raw
construction has `κ+1 ≤ seedBits κ` at every κ, since its public length is positive
and residue width is κ+1. This supplies `κ ≤ seedBits κ` beyond the common cutoff;
the final HasPolyStretch proof includes both conjuncts. No positive-κ premise is
added to the frozen theorem.

## Completed local checks and their limits

| Check | Result and authority |
| --- | --- |
| Fresh owner build | All23 exact owners, including both facades: rc0 and zero errors in both forms. `evidence/build/M2/all-owners/results.jsonl`; all23 source/log/object SHA-256 bindings match the current files, and all records name source4ecc40c. The final recorded owner ended at 2026-11-18T17:38:59.934902+00:00. |
| Stretch theorem axioms | All9 public theorem prints use only propext, Classical.choice and Quot.sound. `evidence/checks/M2-Stretch/summary.json`; its source hash matches the current576-line Stretch module. This scope includes both unchanged reader theorems, four original obligations and three helpers. |
| Stretch frozen statements | Existing frozen statements unchanged; exactly the three listed theorem-only helpers added, as recorded in the same summary. |
| Cumulative steps | All110 saved `step.json` records say CHECKED_PASS. M2 is steps104–110; the prior103 records belong to the completed M1 scope. |
| Source size | 23 owned files,7694 lines; maximum file801 lines, maximum width100. Stretch itself is576 lines, maximum width90. |
| Changed source from M1 | Stretch is the only changed owned file; the other22 source hashes match the saved M1 snapshot. The read-only preparation snapshot binds every current owner and referenced metadata file. |

Fresh M2 probes print **all306 public theorems in12 completed owners**, and all
are standard-only. The19 current headline prints have exactly five standard-only
results (`G4_eval_eq`, `jls_hasComplexity`, `jls_hasPolyStretch`, `lpnNoise_law`,
`PrimeSchedule.nonempty`) and14 retaining sorryAx.
`evidence/checkpoints/M2/axiom-summary.json` binds both fresh logs. This supersedes
the M1-only297-theorem scope without turning either selected probe into a full
stored-constant census.

Fresh `evidence/checks/m2-final/` reports676 ADDED source declarations only,
zero frozen M0 headers changed/removed, exactly six cumulative new helpers,
zero clashes, passing style/sk15/width checks, and no new individual campaign
FAIL/WARN against the base (the campaign command itself retains baseline rc1).
The Phase A boundary scan records no forbidden import or new realization/contract
variant. These are current M2 static results.

The fresh tagged-wrapper audit at `evidence/host/M2-final/slot-summary.json` records
1118 acquisitions, maximum two wrappers because it preserves the known historical
violation,349 post-correction acquisitions with maximum one, post-correction
seriality true, and zero active wrappers. Its qualification excludes global host
or complete child-process-history claims. The two historical instruction breaches
remain disclosed in the full report.

The canonical full stored-constant census, typed statement dump, dependency graph,
four-variant seals and paired controls remain **historical M0 evidence, with the
final fresh gates pending**. The M0 results were88 seals plus96 controls (184 passes)
for the then22 owners; they are not M2 proof passes. The final dynamic inventory
must include Basic and any later owned helper/split modules. No transitive
sorryAx-dependent count is inferred from the42 remaining direct holes.

## Preserved fidelity and current anchors

Keep the exact fidelity, Rule15, target-selection and non-vacuity tables preserved
in `evidence/checkpoints/M1/REPORT.md`, with their original explicit label as
**historical M0 line anchors**. The full deviations remain in the archived M0
report. These contracts/formulas are unchanged by M2; proof status is the status
above, not the historical table's prose or locations.

Use `current-anchor-appendix-M2.md` for the current declaration-identity appendix.
`current-declaration-anchors-M2.tsv` has785 explicit named declaration/field
anchors, and `current-Stretch-anchors.tsv` gives all11 Stretch declarations.
These are source indexes, not kernel-generated declaration or typed census counts.
The other22 files are hash-identical to M1, so their M1 source anchors remain valid.

## Next milestone and retained disclosures

**M3 next means all ten original obligations**, not only the final Claim42 theorem:
five in `Claim42/Load.lean` and five in `Claim42.lean`. The exact frozen names,
current locations and original proof sketches are in `M3-next-obligations.tsv`;
the readable ten-row table is `M3-next-obligations.md`. The final probability bound
must keep its sufficiently-large cutoff independent of the public prime parameter.

Retain the published M1 overlap/reuse and process-limit disclosures without changing
their scope. This includes per-log classification of bounded search results,
harness-error/supersession records, the recorded two-Lean-wrapper overlap and its
correction, and the earlier whole-job subagent-limit breach. This preparation
performs only static reads and temporary report generation; it does not run Lean,
Git, cache tooling, source mutations or agents. No new claim of whole-history
seriality, global host auditing or theorem-search completeness is made.

M2 packaging/publication remains pending. M1's delivery record is
`evidence/delivery/M1.json`; a future M2 delivery hash must come from its actual
published delivery record, not from this source commit or a proposed packaging
commit. The project remains an intermediate Phase A checkpoint.
