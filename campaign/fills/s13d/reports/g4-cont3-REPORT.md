# G4 continuation 3 — checkpoint 1.1b

Outcome: partial. Checkpoint 1.1b is complete. Both public targets remain open, each only through its original body. No new admission or axiom was added. No return-home contract or later checkpoint is landed in this checkpoint.

## Identity and environment

Shared base: `6cfee54474e3d954e3395f9d9eab5d025452a8dd`. Branch: `fill/s13d-g4-cont3`, created at `2026-10-22T07:00:02.779823+00:00`. The cover's ancestor check passed. All five attachment SHA-256 values matched the dispatch, and their repository copies matched after the authorized ancestor-placeholder normalization.

Immediately after branch creation, the two supplied PR #143 patches were applied with `git am`, the one authorized history operation. Patched HEAD: `67966e5571efec32ce62830b7f6378c20eaef81f`; the owned-file blob was exactly `e8353f209617492693aae17c81adc816bad6137e`. This delivery's patch series starts with those two commits and its bundle has only the shared base as prerequisite. No other history operation, push or PR was performed. No code from items 1 or 2 is carried into this branch.

The shared preflight passed: 23,909,351,424 disk bytes free; memory.max 8,589,934,592; anon+kernel+shmem 294,219,776; headroom 8,295,714,816; oom/oom_kill 0. Item-start disk free was 25,530,646,528 bytes. Native Lean reported `failed to locate application`; Part 2's exact executable-path shim was then used, with the source and explanation included. Shim-source SHA-256: `985924ad83d39e108c0a2107bab07e65cdeb88641453508ab5acda115534fba7`. No shim binary is shipped. Scoped wrappers set LEAN_SYSROOT and LAKE_HOME to the official Lean 4.25.0 distribution and LD_PRELOAD only for lean/lake. `/usr/bin/time` was absent; the sequential check runner records `wait4` wall time and max RSS.

There was one clone and one filtered cache invocation for the queue's 40 Mathlib roots / 95-module union, with `TAR_OPTIONS=--no-same-owner`: 35 new downloads, 1,002 unpacked files, exit 0, zero failed downloads and zero empty oleans. No unfiltered cache command or `lake build` was run. All Lean checks use `scripts/lean_check_tree.sh`, one Lean process at a time; screens run separately under `nice -n 10`, one at a time.

The first edit changed only the extension's status paragraph, before re-bootstrap. Re-bootstrap checked all 95 modules, exit 0, with exactly the base's 33 sorry warnings in 14 modules; peak RSS 2,967,624 KiB, summed wall time 547.333 seconds. Logs and the named base sorry list are included.

## Proved characterization

The supplied endpoint statement is true without correction and is proved by `zr_rightPass_post`. For level ℓ = D.1+1, s = zoneStart ℓ, m = zoneCapacity D.1 = 2^ℓ, and q = the incoming scratch head:

- Tape 0's interval [s, s+2m) holds stored virtual blanks in [s, s+m) and empty slots in [s+m, s+2m). Every other tape-0 cell is preserved.
- Tape 1 holds the constant ruler marker on [q, q+m) and is unchanged elsewhere.
- The final heads are s+m on tape 0 and q on tape 1; input position and output are unchanged.
- `zr_rightPass_bounds` proves the stronger envelope 0 ≤ lo₀ and hi₀ ≤ s+2m, together with q−1 ≤ lo₁ and hi₁ ≤ q+m+1. `zr_rightPass_envelope` gives exactly the supplied symmetric tape-0 box.
- `zr_rightPass_tape` proves agreement with the extended zoned tape at every nonnegative cell and with the original zoned tape at every nonpositive cell.
- `zr_rightPassRow` re-wraps the composed pass to a singleton exit using `Contract.ofSegment` through the common adapter. Its precondition, time, post and envelopes are unchanged.

The scratch ruler is the existing constant word of length m. The inherited adjusted walk advances scratch once and walks its tail: tape 0 moves m, scratch moves m+1, then skip-back restores scratch. All endpoint and envelope proofs use published contract equations; no row's trace was re-walked.

## Declaration inventory

Eight new private declarations:

| Declaration | Role |
|---|---|
| `zr_singletonContract` | Re-wrap a contract whose exit set equals one live singleton, preserving all fields. |
| `zr_halfCopy_post` | Common endpoint equation for either constant half-zone copy. |
| `zr_writeHalves_post` | Combine the adjacent half writes with the restored-scratch adjusted walk. |
| `zr_rightPass_post` | Exact supplied right-pass endpoint. |
| `zr_rightPass_bounds` | Strong tape-0 envelope and the requested scratch envelope. |
| `zr_rightPass_envelope` | Supplied symmetric tape-0 envelope. |
| `zr_rightPass_tape` | Right extension / left preservation bridge. |
| `zr_rightPassRow` | Singleton-exit right-pass contract ready for sequencing. |

Four inherited private definitions changed only to call the shared adapter: `zr_rightSeekBackContract`, `zr_rightRulerContract`, `zr_adjustedWalkContract`, `zr_adjustedBackContract`. Their signatures and all five data fields are unchanged. Their old repeated segment/exit wrappers were removed. No other inherited declaration changed, and none was removed. The only public-facing text change is the extension status paragraph, which now states the proved characterization and the remaining work mathematically. The rebalance status is unchanged.

Promotion candidates: the generic singleton-contract adapter and the characterized positive right pass. Existing candidates remain the one-cell leaf, layout bridges, ruler builder, mirror, and a future direction-parameterized adjusted walk. No new leaf was added.

Ownership check: 79 inherited declarations unchanged, including all 18 public declarations and both target statements/bodies. Imports are exactly the original four. Frozen text outside the home and authorized status paragraphs is unchanged. File size is 1,572 lines, 18 public / 73 private declarations; no added line exceeds 100 characters.

## Verification and rule 10

The owned file elaborates with zero errors and exactly the two authorized target sorry warnings, with no new warning. The expanded import-only probe contains the supplied 439 checks plus six further explicit citations (445 total), and has zero errors and zero warnings. An initial literal run of the supplied in-module probe also succeeded; its two warnings came from its copied original target bodies. `probe-cp1.log` is the warning-free import-only re-run.

The full citation inventory is `evidence/g4/external-citations.txt`; the extra six are `Bool.false_eq_true`, `Nat.add_assoc`, `Nat.cast_mul`, `Nat.cast_ofNat`, `Nat.cast_pow`, and `abs_of_nonneg`. New TCSlib citations are within the supplied inventory: the `Contract.seq`/`ofSegment` field equations, catalog contract post/lo/hi equations, `Cfg.mapState` field equations, `seekPost`/`sweepPost` field equations, `zoneCapacity_eq`, `zoneStart_succ`, `two_le_zoneStart`, and `zonedTape_extend`. Existing own helpers supply all intermediate compatibility facts.

The final seal covers the entire private home, with the maintainer's 56-definition seal plus `Cfg.SameOutside` (57 total), listed in `evidence/g4/seal-cp1.txt`. It elaborated with zero errors and only the two original target warnings. Every new `rw`/`simp`/`simpa` argument and definitional closure was also inspected: external TCSlib definitions are never unfolded; reductions are confined to owned definitions, local bindings, and standard Lean/Mathlib primitives. Rule 11's diff scan found none of the six R3 canonical row names, and no other-file private citation. No seam, phase host, iteration, embedding transport or row trace was re-proved.

Axiom prints cover every new/changed private (12) and both targets. The 12 privates use only `propext`, `Classical.choice`, and `Quot.sound`; each target additionally has `sorryAx` only through its unchanged open body. Lint: `0 FAIL, 31 WARN over 39 files`, equal to the patched baseline.

The checkpoint uses the owned-file and downstream facade checks as its permitted final sweep (both exit 0; owned file peak RSS 2,193,756 KiB). The full 95-module final sweep will be run for the final item delivery.

## Open work and continuation

- `exists_zoneExtendTM` remains open. **Proof sketch:** sequence the characterized right pass with the unique-one-cell-field return-home loop using public rounds and `Round.iterate`; seek left under local tape agreement, parameterize the ruler walks by direction, write the left halves, handle level zero with the existing one-cell leaf, clear the ruler, and assemble the exact `HeadBox` contract with geometric time bound.
- `exists_zoneRebalanceTM` remains open. **Proof sketch:** build the two-escape zone scan with a unary zone count, compose guarded column copies/repacking at each level, use the inherited four-side-pass cascade reordering with the home move, mirror the opposite direction, clear scratch, and assemble the frozen endpoint, time and envelope.

The left-pass displacement choice remains the brief's full-ruler walk followed by an adjusted walk, totaling 2·2^ℓ+1; no left machine has yet been composed, and no machine-level ℓ=1 claim is made. The inherited arithmetic places that level's new outer end at −8. Ground-rule escalations: none.

## Duplication and package

Before: `declarations screened: 838; copy pairs (target reproduces >= half of source): 478; reproduced text: 137,237 chars`.

After: `declarations screened: 846; copy pairs (target reproduces >= half of source): 477; reproduced text: 136,473 chars`.

No new owned cross-file pair and no new pair at or above 90%. Five new in-file pairs:

| Target reproduces source | Score | Justification |
|---|---:|---|
| `zr_rightPass_bounds` / `zr_rightPass_time` | 563/665, 85% | The two distinct field calculations traverse the same composite and therefore list the same owned subcontracts and catalog field APIs. The bounds add the head endpoints and inequalities; no trace or induction is copied. |
| `zr_rightPass_post` / `zr_rightPass_pre` | 85/140, 61% | Extracting the first phase's precondition uses the same short seam-precondition reduction before the independent endpoint comparison. |
| `zr_rightPass_bounds` / `zr_rightRuler_pre` | 113/189, 60% | Common contract and map-state field names in the envelope expansion; the precondition and envelope arguments are different. |
| `zr_writeHalves_post` / `zr_rightPass_pre` | 75/140, 54% | Short precondition projections into a sequential contract, followed by the new two-write interval proof. |
| `zr_writeHalves_post` / `zr_rightRuler_pre` | 101/189, 53% | The shared field-reduction vocabulary for preconditions; no repeated semantic proof. |

Six old adapter pairs disappeared. The former 81% top adapter pair is now 63%. Full outputs and the keyed delta are included. **new copies: none**.

This checkpoint is `fill-s13d-g4-cont3-cp1.zip`; its SHA-256 is given with the delivery and in the session report. The zip contains this report, the committed source, the base-relative patches and bundle, shared/bootstrap/check/axiom/seal/probe/lint/screen logs, reproducible audit inputs, and `SHA256SUMS`. No toolchain, cache, compiled object, or shim binary is included.
