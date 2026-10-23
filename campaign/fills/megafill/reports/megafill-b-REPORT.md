# Megafill B — session report

Outcome: items 1 and 2 are complete within their briefs; item 3 is partial through checkpoint 1.1b. The session stopped after loss of its working environment. All three delivered item archives were recovered byte-for-byte and verified. No item is “not started.”

All times below are UTC. Shared base: `6cfee54474e3d954e3395f9d9eab5d025452a8dd`.

## Queue, branches and times

| # | Item and branch | Outcome | Branch start | Item end |
|---|---|---|---|---|
| 1 | U2-S cont1 — `fill/u2s-startup-cont1` | Complete, proved modulo exactly the authorized `Turing.exists_seamLayoutTM`; checkpoints 1–4 complete | 2026-10-22T05:14:34.306136+00:00 | 2026-10-22T06:14:22.325525+00:00 |
| 2 | B6 F5 cont1 — `fill/b6-rulerdevice-cont1` | Complete; device and host proved without admitted dependencies; checkpoints 2 and 3 delivered | 2026-10-22T06:15:31.325924+00:00 | 2026-10-22T06:58:51.233487+00:00 |
| 3 | G4 cont3 — `fill/s13d-g4-cont3` | Partial; checkpoint 1.1b complete, archived as cp1; both public targets remain open | 2026-10-22T07:00:02.779823+00:00 | Closed at recovery observation, 2026-10-22T16:29:20.722209+00:00; exact workspace-loss time unknown |

G4's last durable commit was made at 2026-10-22T07:31:07Z and its checkpoint was saved at 2026-10-22T07:31:14.339066Z. The interval to closure is not a claim of continuous active work. Return-home checkpoint 1.2 was in progress after cp1; its unshipped scratch source and logs did not survive. It is not counted as completed or included in this delivery.

| Item | Final delivered commit | Item archive |
|---|---|---|
| U2-S | `8e1aee0fc57a54b26678355396bda5922f71a49e` | `fill-u2s-startup-cont1.zip` |
| F5 | `0f57ba49bf3ca8e5017dfed11ea010d723498284` | `fill-b6-rulerdevice-cont1.zip` |
| G4 | `01bcc6e08d977a7a33a181dd2b7ef72c0828cf12` | `fill-s13d-g4-cont3-cp1.zip` |

G4 is delivered under its brief's explicit early-stop rule: “Deliver the latest checkpoint zip if the session ends early.” Its original checkpoint archive is unchanged; no full-completion archive or later checkpoint is claimed.

## Archive SHA-256

| Archive | SHA-256 |
|---|---|
| `fill-u2s-startup-cont1.zip` | `95a0e169f60e29488a1187bd829d375d427d2923459d4d292c008869371dbdd4` |
| `fill-b6-rulerdevice-cont1.zip` | `76f4550161573b3edbaaaf83179093575e7b06eb2efea2f3d89efafa0f38cf28` |
| `fill-s13d-g4-cont3-cp1.zip` | `fe1398e55eca7625fc437b1153326e8b286da16403999e876648f052c71315e9` |

Recovery rechecked all ZIP CRCs and every entry named by each internal `SHA256SUMS`: 122 entries for U2-S, 92 for F5, and 70 for G4. All matched. `recovery-verification.json` records this check. Each item ZIP retains its source, item REPORT.md, base-relative patches and bundle, and verification evidence.

## Shared preflight and setup

Preflight at 2026-10-22T05:10:08.491441+00:00 passed:

| Measurement | Value |
|---|---:|
| Available processors (`nproc`) | 9 |
| Clone/scratch filesystem | overlay |
| Initial free disk | 23,909,351,424 bytes |
| `memory.max` | 8,589,934,592 bytes |
| `anon + kernel + shmem` | 294,219,776 bytes |
| Computed memory headroom | 8,295,714,816 bytes |
| `oom` / `oom_kill` | 0 / 0 |

The initial 12 GiB disk and 4 GiB headroom floors passed. Full counters and filesystem records are in each archive's shared preflight logs. G4's item-start disk was 25,530,646,528 bytes.

The single clone checked out `complexity/arora-barak-ch3-4`, not main. The cover's ancestor check passed with HEAD equal to the shared base. All five attachment SHA-256 values matched the dispatch, and repository copies matched after the permitted ancestor-placeholder normalization; `evidence/logs/attachment-verification.log` records each value.

Official Lean 4.25.0 initially failed with `failed to locate application`. Only then was Part 2's exact shim used. Source SHA-256:
`985924ad83d39e108c0a2107bab07e65cdeb88641453508ab5acda115534fba7`.

Scoped Lean/Lake wrappers set:

- `LEAN_SYSROOT=/workspace/scratch/f441fd79989b/lean-4.25.0-linux`
- `LAKE_HOME=/workspace/scratch/f441fd79989b/lean-4.25.0-linux`
- `LD_PRELOAD=/workspace/scratch/f441fd79989b/executable-path.so`, only for Lean/Lake.

The shim source is included; its compiled binary is not. Module timing used `wait4` wall time and maximum RSS because `/usr/bin/time` was absent.

The queue's one filtered cache invocation used the union of all three order lists: **95 modules, 40 direct Mathlib roots**, with `TAR_OPTIONS=--no-same-owner`. It exited 0: **35 new downloads, 1,002 unpacked files, zero failed downloads, zero empty oleans, no retry**. The root-import probe passed and package URLs/revisions matched the manifest. No unfiltered cache command or project `lake build` was run.

Each item started independently from the shared base, made its first edit, then re-bootstrapped its whole 95-module order list. Item 3 immediately applied PR #143's two supplied patches by the authorized `git am`. Its patched HEAD was `67966e5571efec32ce62830b7f6378c20eaef81f`, and its owned-file blob matched `e8353f209617492693aae17c81adc816bad6137e`. No code passed between item branches. One Lean process and one screen ran at a time; all Lean checks used `scripts/lean_check_tree.sh`.

## Results and surviving verification

**U2-S.** `Turing.exists_selfStartupTMK` is filled; its only admitted dependency is the explicitly authorized seam-layout theorem. All 95 final modules passed, with 32 expected sorry warnings in 14 modules, peak RSS 2,939,516 KiB and summed module wall time 520.325 seconds. The 32-definition seal and 121-name probe passed. Axiom prints cover all 39 private declarations and three public targets. Lint: 0 FAIL, 64 WARN over 82 files. All eleven new screen pairs are in-file and below 90%; no new cross-file pair. Full details and the exact dependency explanation are in the item's report.

**F5.** `Turing.exists_rulerDeviceTM` and `Turing.exists_rulerHostTM` are proved without admitted dependencies. All 95 final modules passed, with 31 expected sorry warnings in 13 modules, peak RSS 2,944,700 KiB and summed module wall time 539.971 seconds. The 17-definition seal, 148-name probe and 35 axiom prints passed. Lint: 0 FAIL, 31 WARN over 39 files. No new cross-file copy or pair at or above 90%.

**G4.** Checkpoint 1.1b proves the positive right pass's exact endpoint, tape agreement, stronger head bounds, and supplied envelope, and supplies the singleton-exit adapter for further composition. Eight private declarations were added and four inherited adapters refactored. Both public target statements and their original admitted bodies remain unchanged.

G4's bootstrap passed all 95 modules with the exact base set of 33 sorry warnings in 14 modules; peak RSS 2,967,624 KiB and summed wall time 547.333 seconds. The checkpoint's permitted owned-file and downstream-facade checks passed; owned-file peak RSS was 2,193,756 KiB. The 57-definition seal and 445-name import-only probe passed. The 12 new/changed private declarations use only `propext`, `Classical.choice`, and `Quot.sound`; both targets retain `sorryAx` through their own unchanged bodies. Lint: 0 FAIL, 31 WARN over 39 files. No new owned cross-file pair; all five new in-file pairs are below 90% and justified in the report.

No post-checkpoint full 95-module final sweep was performed for G4. The surviving checkpoint uses the owned-file/facade sweep allowed by its brief. Missing prerequisites after workspace loss prevented further Lean checks; no check was run against a missing tree.

## Interruption and remaining work

Recovery found the original clone, toolchain, runtime wrappers, dependency cache, and unshipped return-home draft absent. The precise cause and reset time are unknown. This is an environment-loss interruption, not a mathematical obstruction, a claimed resource-floor failure, or an OOM finding. Items 1 and 2 stand unchanged. The last item's surviving checkpoint is the final partial delivery for this run.

The cover and addendum prescribe one shared host/clone/cache; the G4 brief specifically provides checkpoint delivery for a lost workspace. This recovery did not create another clone, refetch a cache, reuse another session's build tree, perform a history operation, or reconstruct unverified proof text.

- `Turing.exists_zoneExtendTM` remains open. **Proof sketch:** compose the characterized right pass with the unique-one-cell-field return-home loop using public rounds and `Round.iterate`; seek left under local tape agreement, parameterize ruler walks by direction, write the left halves, handle level zero with the existing one-cell leaf, clear the ruler, and assemble the exact head box and geometric time bound.
- `Turing.exists_zoneRebalanceTM` remains open. **Proof sketch:** build the two-escape zone scan with a unary zone count; compose guarded column copies and repacking at each level; use the inherited four-side-pass cascade reordering and home move; mirror the opposite direction, clear scratch, and prove the frozen endpoint, time and envelope.

Checkpoint 1.2 and all later G4 checkpoints remain undelivered. Their continuation requires a newly established Lean environment. There was no return to an earlier item, and no push or PR was made.
