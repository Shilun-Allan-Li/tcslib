# §12.6 framed catalog fill — completed 5/5

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Requested branch checked out: `complexity/arora-barak-ch3-4`; working branch: `fill/s12-framed`.
- Recorded base: `0658eb8c73271de708557ce1b72e6223d32fb719` (the brief-issuing commit immediately after `841122fc6d39657f764e5b46e9756121e98e879e`).
- Delivery commit: `9f557a316508068c99feec432f5981f75cdf28f8`. No rebase, push, or PR.
- Only tracked change: `TCSlib/Complexity/TuringMachine/Build/Catalog.lean`.
- Binding brief, statement findings, resolutions, and repository policy read in full.

## Proof results and sanctioned changes

All five audited statements are proved exactly as frozen:

| Framed contract | Exact time | Canonical row now specializing it |
|---|---|---|
| `transferTM_run_ofCfg` | `2 * w.length + 2` | `transferTM_run` |
| `copyTM_run_ofCfg` | `2 * w.length + 2` | `copyTM_run` |
| `clearTM_run_ofCfg` | `2 * w.length + 2` | `clearTM_run` |
| `incrementTM_run_succ_ofCfg` | `2 * (w.takeWhile id).length + 2` | `incrementTM_run_succ` |
| `incrementTM_run_overflow_ofCfg` | `2 * w.length + 2` | `incrementTM_run_overflow` |

**Flagged reordering:** moved the existing framed-contract section before the
canonical run/space rows. Every public statement remains byte-identical.
**Flagged canonical proof-body swaps:** the five rows listed above each cite
its framed theorem at `Cfg.ofWords`; transfer/copy use the original blank
destination hypothesis to identify the complete final tape, and successful
increment uses width preservation.

Each routine has one generalized forward/turn/return trace over the arbitrary
initial configuration. Copy and transfer still share `catalogCopyF` and
`catalog_copy_forward`. Both increment verdicts share `catalog_increment_trace`.
The generic `catalog_trace_run` is reused byte-identically. No canonical trace
is retained alongside a framed copy. The existing increment split/value lemmas
are reused; the success proof identifies the split length with the audited
`takeWhile` length.

The trace records retain the initial input position and output. All tape
coordinates remain integers. The trace proves every-time head containment,
first arrival at the live exit, precise final tape contents, and the stationary
post-exit tail, including empty words and arbitrary destination contents.

**Space rows:** the four `*_spaceUsedByTape` proof bodies are adapted to
specialize the same generalized traces at canonical configurations. They keep
the existing integer-interval cardinality argument and apply at every time,
including after exit. Their statements are unchanged. `compareTM`, its traces,
and both compare contracts are byte-identical. No imports were added, and no
optional permanent regression declarations were added.

## Private declarations and freeze

Private declarations: **384 before → 384 after; delta 0**.

| Disposition | Private declarations |
|---|---|
| Generalized in place | `catalogClearF`, `catalogClearR`, `catalog_clear_trace` |
| Generalized in place | `catalogCopyF`, `catalogCopyR`, `catalog_copy_forward`, `catalog_copy_trace` |
| Generalized in place | `catalogTransferR`, `catalog_transfer_trace` |
| Generalized in place | `catalogIncF`, `catalogIncR`, `catalog_increment_trace` |
| Generalized in place | `catalog_write_take`, `catalog_write_middle` |
| Removed as obsolete | `catalog_erase_take` |
| New local frame definition | `catalogTape` |

The new `catalogTape` preserves the original tape outside a finite translated
word interval; it replaces the obsolete canonical erasure helper in the private
count. Zero new copied declarations or proof bodies; no requested shared lemma
or unresolved frontier.

`evidence/surface-freeze.log` records the source comparison: all **44 explicit
public statements** unchanged; the **30 public declarations outside the 14
authorized proof edits** unchanged in full; every other private declaration
unchanged. The scoped checker is included as `evidence/verify_surface.py`.

## Duplication census

Both required runs used the unmodified script:

```sh
python3 -I audits/evidence/retrofit/r1-public-proof-screen.py <repo-root>
```

Pass 4 totals:

| File | Before members/total | After members/total | Member delta |
|---|---:|---:|---:|
| Composition | 6/19 | 6/19 | 0 |
| Primitives | 173/272 | 173/272 | 0 |
| TimeConstructible | 20/21 | 20/21 | 0 |
| Loop | 98/199 | 98/199 | 0 |
| Wrappers | 19/29 | 19/29 | 0 |
| Catalog | 318/428 | 318/428 | 0 |

**No file's duplication member count grew.** Complete before/after outputs and
the checked comparison are included under `evidence/`.

## Verification

Lean 4.25.0; mathlib pin `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
Every Lean check used `scripts/lean_check_tree.sh`; no `lake build` was run.
The pinned toolchain and dependency cache were reused. The current `Build/Loop`
was rebuilt before Catalog, and the host's existing application-path compatibility
shim was used without modifying Lean, the kernel, or the checker script.

| Check | Result |
|---|---|
| `Build/Catalog` | Exit 0, fresh olean, zero errors, zero sorry warnings |
| `Build/Zone` | Exit 0; two unchanged baseline admissions |
| `Codes2Tape` | Exit 0; one unchanged baseline admission |
| `TuringMachine` facade | Exit 0; no own admissions |
| Axiom probe | Exit 0; all ten run rows and all 325 public/generated Catalog constants checked |
| Campaign style lint | `style_lint: 0 FAIL, 4 WARN over 11 files` |
| Patch replay | Applied to the recorded base in an isolated index; entire tracked tree equals delivery commit |
| Bundle verification | PASS; recorded base is the prerequisite |

All ten named run-row axiom prints are exactly
`[propext, Classical.choice, Quot.sound]`. The exhaustive public/generated
constant check admits only those three axioms and finds **no `sorryAx`**.
The complete prints are in `axioms.log`; the checked probe is
`evidence/S12Axioms.lean`.

Downstream own admissions remain `exists_zoneShiftInTM`,
`exists_zoneShiftOutTM`, and `exists_uniformMachineCode2`. The requested modules'
import closure additionally retains the pre-existing `CounterProgRun.lean: sim_run_of_regs_le`
and `NDCodes.lean: exists_effectiveNDMachineCode` admissions. None was modified or
introduced by this patch; no Catalog public constant depends on them.

The four style warnings are the existing oversized-file categories (Catalog,
Loop, Primitives, Zone); this batch keeps the commissioned shared-home scope.
Ordinary Lean linter warnings remain in the complete sweep log.

Final sweep tail:

```text
PASS TCSlib/Complexity/TuringMachine/Build/Catalog (exit 0; fresh olean; zero errors; zero sorry warnings)
CHECK TCSlib/Complexity/TuringMachine/Build/Zone
TCSlib/Complexity/TuringMachine/Build/Zone.lean:1109:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Zone.lean:1145:8: warning: declaration uses 'sorry'
PASS TCSlib/Complexity/TuringMachine/Build/Zone (exit 0)
CHECK TCSlib/Complexity/TuringMachine/Codes2Tape
TCSlib/Complexity/TuringMachine/Codes2Tape.lean:859:8: warning: declaration uses 'sorry'
PASS TCSlib/Complexity/TuringMachine/Codes2Tape (exit 0)
CHECK TCSlib/Complexity/TuringMachine
PASS TCSlib/Complexity/TuringMachine (exit 0)
```

## Package and replay

Contains this report, the full modified source, one `git format-patch`, an
incremental git bundle, complete final sweep and axiom logs, census outputs,
freeze/lint/packaging evidence, and `SHA256SUMS` (all files except the manifest
itself). The ZIP has no enclosing directory.

From a checkout at the recorded base, use the patch series or fetch the bundle's
`fill/s12-framed` branch. Replay the module checks in the order above. To replay
the axiom probe, copy `evidence/S12Axioms.lean` to the repository root and run:

```sh
bash scripts/lean_check_tree.sh S12Axioms
python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build
python3 evidence/verify_surface.py <repo-root> 0658eb8c73271de708557ce1b72e6223d32fb719
```

Catalog SHA-256: `2f28360cdb77235f8a1a732f084f032824ac5f12adf773f6b8ee6874ea5506e3`.
