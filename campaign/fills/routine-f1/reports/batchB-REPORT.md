# §12 F1 Batch B — seam composition and release

**Complete: 11/11 targets filled.** No new admissions, axioms, public declarations, or statement changes. Delivery is the flat `fill-s12-f1-B.zip`; no push or pull request was made, and `lake build` was never run.

## Provenance and scope

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Requested starting branch: `complexity/arora-barak-ch3-4`.
- Recorded base: `42d524b665f1fc856fe6f60a27a7d7ecced91b71` (the commit adding the matching `briefs/routine-f1-batchB.md`; its parent is the brief's issuance commit `f7f4f0f7`).
- Working branch: `fill/s12-f1-B`; no rebase.
- Delivery commit: `4938f0fe9610c724d6c011f44013307ac285303a`.
- Only changed repository file: `TCSlib/Complexity/TuringMachine/Build/Seam.lean`.
- Full source: 696 lines, 36,665 bytes. The coherent shared decomposition stays in the sole owned file.
- Instructions read: the matching Batch B brief, repository policy/workflow, all three routine-infrastructure audit reports, and their resolutions.

## Proof order and discharge map

The general-configuration trio was filled first, then the canonical instances, additive/max space corollaries, and release contracts, in the brief's order. To preserve the public declaration order (which places canonical statements before the general ones), the general proofs live in private cores. Each general public theorem is a wrapper around its core; the canonical theorem specializes that same core using `seam_ofWords_mapState`. No canonical theorem has an independent lockstep proof.

| Target | Discharging proof |
|---|---|
| `seamCompTM_run_ofCfg` | `seamComp_run_general`: left lockstep, one exact dispatch, right lockstep, then the phase-two endpoint |
| `seamCompTM_firstReturn_ofCfg` | `seamComp_firstReturn_general`: left/right constructor separation and the transported phase-two cut |
| `seamCompTM_visitedByTapeHead_ofCfg` | `seamComp_visited_general`: split each image witness at dispatch; no phase-two endpoint hypothesis |
| `seamCompTM_run` | Canonical instance of `seamComp_run_general` |
| `seamCompTM_firstReturn` | Canonical instance of `seamComp_firstReturn_general` |
| `seamCompTM_visitedByTapeHead` | Canonical instance of `seamComp_visited_general` |
| `seamCompTM_spaceUsedByTape_le_add` | Cardinality monotonicity and the union-cardinality inequality |
| `seamCompTM_spaceUsed_le_add` | Sum the per-tape inequality |
| `seamCompTM_spaceUsedByTape_le_max` | Each phase visits its initial origin; the idle singleton is contained in the other phase's set |
| `seamReleaseTM_firstReturn` | Execute the fresh step, transport every positive-time run, and exclude time zero by constructor disjointness |
| `seamReleaseTM_visitedByTapeHead` | Pointwise head equality at zero and every positive time, then equality of finite images |

The two full-configuration trajectory identities required by the inherited audit contract are exactly `seamComp_left` and `seamComp_right`. Dispatch preserves every non-control field of an arbitrary configuration. The right lockstep and release lockstep include halting and post-halt times. Thus the audit's S7 execute-first return and S9 displaced-head/nonempty-output cases are instances of the proved contracts; no canonical-seam assumption was added to a general theorem.

## New declarations

All 13 are private lemmas; none remains admitted:

1. `seamComp_step_left` — one-step left correspondence away from the exit.
2. `seamComp_step_right` — unconditional one-step right correspondence.
3. `seam_stationary_apply` — a stationary, silent, write-free action changes only control.
4. `seamComp_dispatch` — dispatch on an arbitrary live exit configuration.
5. `seamComp_left` — inclusive left-prefix run correspondence under the cut.
6. `seamComp_right` — right run correspondence at every offset after dispatch.
7. `seamComp_run_general` — the shared general endpoint proof.
8. `seamComp_firstReturn_general` — the shared general exclusion proof; endpoint hypotheses are unnecessary for this exclusion alone.
9. `seamComp_visited_general` — the shared general visited-set containment.
10. `seam_ofWords_mapState` — canonical state mapping, proved by reflexivity.
11. `seamRelease_fresh_step` — the fresh state executes the source anchor's action.
12. `seamRelease_step_right` — one-step correspondence in the right copy.
13. `seamRelease_run_pos` — source-run correspondence at every positive time.

Requested shared lemmas: **none**. Escalations: **none**. Remaining targets/frontier: **none**. No existing docstring or attribution was edited; new helper docstrings explain their proof steps.

## Verification

All checks completed successfully on 2026-10-09 UTC.

| Gate | Result |
|---|---|
| Prescribed 65-module bootstrap | Exit 0; zero errors; one untouched pre-existing admission in `CounterProgRun.lean:343` |
| Five additional facade dependencies | Exit 0; zero errors; 48 untouched pre-existing admissions (Embed 13, Catalog 32, NDCodes 1, QBF 1, QBFEncoding 1) |
| Final owned-file check | Exit 0; fresh nonempty olean; zero errors; zero sorry warnings |
| Final TuringMachine facade check | Exit 0; fresh nonempty olean; zero errors |
| All eleven axiom prints on the final fresh tree | Four footprints `[propext, Quot.sound]`; seven `[propext, Classical.choice, Quot.sound]`; no `sorryAx` |
| Incremental git bundle | `git bundle verify` succeeds |

Final sweep log tail:

```text
PASS TCSlib/Complexity/TuringMachine/Build/Seam: exit 0, fresh nonempty olean
CHECK TCSlib/Complexity/TuringMachine
PASS TCSlib/Complexity/TuringMachine: exit 0, fresh nonempty olean
```

The five remaining diagnostics in the owned file are only unused-variable warnings for redundant hypotheses in frozen signatures: canonical `firstReturn.h₂`, canonical `visitedByTapeHead.h₂`, general `firstReturn.h₂` and `firstReturn.hq`, and release `firstReturn.hc'`. They are not admissions or errors. Existing module/docstring labels mentioning the statement-skeleton phase were retained under the brief's docstring freeze.

The statement-preservation check (`freeze-check.log`) confirms byte-identical public theorem signatures and machine definitions, unchanged public declaration inventory/order, preservation of all 15 original comments/docstrings, unchanged imports/options/namespace variables, and exactly one changed repository path. `git diff --check` passes.

## Environment and reproduction

Lean is the pinned official **4.25.0**, commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`; mathlib is pinned at `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.

This environment exposes executable discovery at `/proc/self/exe`; Lean's numeric self-PID path did not work. The included `app_path.c` is a narrow runtime compatibility shim: it maps only this process's own executable-path lookup to `/proc/self/exe` and passes every other `readlink` call through unchanged. It changes no Lean executable, kernel, source, proof term, or compiler option. Build it with `gcc -shared -fPIC app_path.c -ldl -o app_path.so`, then set `LD_PRELOAD` to that shared object's absolute path if reproducing in this same environment. Ordinary hosts do not need it.

The authorized `lake exe cache get` setup was narrowed to the 32 external Mathlib roots used by the bootstrap/import closure after the full-cache attempt was interrupted; it completed successfully and unpacked 969 cached modules. No dependency source, manifest, checker script, or toolchain source was modified.

The supplied 65-module bootstrap order predates six imports now wired into its facades: `Build/Embed`, `Build/Seam`, `Build/Catalog`, `NDCodes`, `Formulas/QBF`, and `Formulas/QBFEncoding`. The owned module was checked during proof iteration; the other five unchanged modules were checked separately before their importing facades. This supplements the prescribed order without changing it. Their pre-existing admissions remain untouched and are not dependencies of the eleven completed proofs, as the axiom prints confirm.

## Archive and integration

- `Seam.lean`: full modified source, to place at the owned repository path above.
- `0001-Fill-section-12-seam-composition-and-release-proofs.patch`: one-commit `git format-patch` series against the recorded base; integrate with `git am -3`.
- `fill-s12-f1-B.bundle`: verified incremental bundle; its prerequisite is the recorded base, and its `HEAD` is the delivery commit.
- `sweep.log`, `axioms.log`, and `Axioms.lean`: final checks and reproducible axiom-print program.
- `bootstrap.log`, `bootstrap-extra.log`: prerequisite elaboration evidence.
- `freeze-check.log`, `bundle-verify.log`, and `app_path.c`: preservation, bundle, and environment evidence.
- `REPORT.md` and `SHA256SUMS`: this report and checksums of every other archive member.

All archive members are at the ZIP root. Verify with `sha256sum -c SHA256SUMS` after extraction. The archive contains no generated Lean binaries or dependency trees.
