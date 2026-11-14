# Arora–Barak ch. 3–4 maintainer handoff

Ruled by the user on 2026-11-04: the campaign moves to a cloud machine like the Pass–Shelat line,
with the exchange in the `arora-barak-ch3-4/` folder of the orphan branch
`exchange/pass-shelat-ch5-8`. The handoff point is **quiescent**: the heavy local replays finish
on the Mac first. Read `WORKFLOW.md` (beside this file) first; it holds the standing rules. The
long-form state is in `campaign/backlog.md`, and the duplication debt in
`campaign/duplication-ledger.md`.

## 0. Current state (2026-11-14; authoritative)

Seyoon alone merges source, dispatches and rules on design or debt. Records
only go directly after fetch/rebase. The latest merge is #296 (RO-1, gate 132).
Campaign Lean is `5ab222167eb12664d97d255766c5def15b6d5d50`. Its replay output
is the cloud snapshot `oleans-c5ab2` (876 objects); use it whole. See
campaign/status/2026-11-14-merge-296/. Earlier merges are in the table.

| PR / gate | Current state |
|---|---|
| #300 / 133 | **Not yet clear to merge.** Readers for Call, Clean and the Oblivious consumers at `829648df` (60 readers and the `obliviousScheduleCfg` transport; rulings 2026-11-14). Replay, seals, controls, screen done; Codex gate 133 being staged. See campaign/gates/133-call-clean-oblivious-readers/. |
| #296 / 132 | **Merged** at `5ab222167eb12664d97d255766c5def15b6d5d50` (2026-11-14). Gate closed (round 3 CLEAR). Its replay output is the campaign snapshot `oleans-c5ab2` (876 objects; campaign/status/2026-11-14-merge-296/). |
| #251 / 129 | **Merged** at `4fff1ea826606070b86d0057052c20f3504b19e6` (2026-11-12). Gate closed (round 5 CLEAR). Its replay output is the campaign snapshot `oleans-c4fff` (876 objects; campaign/status/2026-11-12-merge-251/). |
| #253 / 131 | **Merged.** Gate closed. Exact 404-module replay adopted at `e9478d452d5830adbe70ab77542224f326296a3e`. |
| #242 / 122 | **Merged** at `7b6bd1685a1436313dfbc13ce191f40c7dd065d3` (2026-11-12). Gate closed. Its replay output is the campaign snapshot `oleans-c7b6b` (campaign/status/2026-11-12-merge-242/). |
| #241 / 121 | **Merged** at `3a10a32e8975b79621873626198356fdea61e988` (2026-11-12). Gate closed. Its replay output is the campaign snapshot `oleans-c3a10` (campaign/status/2026-11-12-merge-241/). |
| #252 / 130 | **Merged.** Gate closed and actual335 snapshot adopted before the Ladner merge. |
| #249 / 128 | **Merged** as Ladner statement scaffold. Gate closed and current actual2 replay passed. |
| #254 | **Merged** (2026-11-11, `2088f98e`), tooling only, no Lean diff. |

Gates 123–127 are closed and #243–#247 have merged.

Roadmap: 26/26 previously tracked headlines and 19 additional checked
closures without sorryAx. Book-form Theorem 3.1, SPACE(n+1) ≠ NP and F6
are proved and merged. Ladner's six mathematical holes and packaging remain
the main open theorem. No fill is dispatched. RD-2/H6 remains separately
held (41 direct admissions in the recorded scopes, outside the merged TQBF
proof). See campaign/status/2026-11-08-roadmap-readiness/.

Pending design: SAT PolyTimeBlockLoop import. **LD9 approved (Seyoon, 2026-11-14):** `SAT_exists_linear_verifier` (ClassNP/SAT, after `SAT_mem_NP`), own gated PR. Codex drafts the six Ladner fill routes (`campaign/items/ladner/fill-routes-request/brief.md`).
Scheduled: a reader PR for `Call.call_run`/`Clean.cleanTM_run` and the Oblivious consumers `obliviousSchedule_ready`/`_halts` (ruled out of #242's scope 2026-11-12; ledger "Gate 122 held Call and Clean fronts").
**RO1 home ruled (Seyoon, 2026-11-12): `Deterministic`** (the alternative in
`campaign/items/dedup/overnight-2026-11-08/review/ro1-deterministic-option/`),
superseding the 2026-11-06 `CfgFacts` ruling. The generic
`Turing.MultiTapeTM.runFrom_one` goes beside `runFrom_zero` and
`runFrom_succ_eq_step`, with no import changes, and is added to the file's
list of local modifications. The re-point scope ruled on 2026-11-06 stands.
It is rebuilt on the campaign after #251, #241 and #242 merge (it shares 13 files
with them), then gets its own replay and gate. **Rebuilt as #296 (gate 132), merged 2026-11-14.** The archived `CfgFacts` draft is superseded. The approved
Hardness CfgFacts import stays separate. Next free gate 135 (134: the SAT linear-verifier reader). Use complete
snapshots, approved wrappers, local3/machine5 and one screen lock. Preserve
the original campaign checkout's example and all shared inbox originals.

## 1. Starting a session on a new machine

**Current Mac setup:** use `campaign/status/2026-11-06-mac-bootstrap/setup.md` and the existing
scratch environment/worktree aliases. The instructions below retain the previous cloud recipe;
the current native toolchain is Lean 4.25.0, with `.lake/packages` linked to the original checkout.

1. **Environment.**
   - Network access to Mathlib's cache hosts (`lakecache.blob.core.windows.net`,
     `mathlib4.lean-cache.cloud`), the same custom environment as the Pass–Shelat line.
   - `TCSLIB_SCRATCH` set to a scratch directory with about 15 GB free, and `TCSLIB_REPO` to the
     clone. The exchange worktree's path, `$TCSLIB_SCRATCH/wt-xch/arora-barak-ch3-4`, goes in
     `TCSLIB_EXCHANGE` for `stage.sh`.
2. **Checkouts.**
   - Clone `https://github.com/Shilun-Allan-Li/tcslib` and fetch with
     `+refs/pull/*/head:refs/remotes/origin/pr/*`, so that the name searches see every PR head.
   - **The records worktree:** `git worktree add --detach $TCSLIB_SCRATCH/wt-hk
     origin/complexity/arora-barak-ch3-4`. The tools assume `wt-hk` under the scratch dir. Push
     records with `git push origin HEAD:complexity/arora-barak-ch3-4`, after
     `git fetch && git rebase origin/complexity/arora-barak-ch3-4`.
   - **The exchange worktree:** `git worktree add --detach $TCSLIB_SCRATCH/wt-xch
     origin/exchange/pass-shelat-ch5-8`. Touch only `arora-barak-ch3-4/`, and pull with rebase
     before every push.
   - **Every worktree** needs `mkdir -p <wt>/.lake && ln -s <clone>/.lake/packages
     <wt>/.lake/packages`.
3. **Mathlib.** In the clone, run `lake exe cache get`, never `lake build`. Then check that
   `.lake/packages/mathlib/.lake/build/lib/lean/Mathlib` exists. The fill-environment addendum
   (`campaign/standards/fill-environment-addendum.md`) records the cloud recipe the fill workers
   use: a narrowed fetch, the manifest check, and the Lean start-up fallback.
4. **The first snapshot.** `bash wt-hk/devtools/seyoon/bootstrap-snapshot.sh wt-hk
   oleans-cloud0` compiles the root's import closure, 886 modules, one at a time. The local
   Mac's 313-module replay took 16 minutes, and the VM is two to three times slower. The log's
   first line names the commit. Later replays chain from this snapshot with
   `devtools/seyoon/mk-next.sh`, so give it as `<snapshot-tree commit>`.
5. **Copy-text screens:** `scripts/copy-text-screen-v3.py`, one at a time under
   `$TCSLIB_SCRATCH/locks/screen`.

6. **Cloud specifics, learned 2026-11-05** (the first cloud session):
   - **Profile edits are refused**, so the variables live in `$TCSLIB_SCRATCH/env.sh` (with elan's
     `bin` on `PATH`); source it at the start of every command. elan is installed with
     `--no-modify-path` and no default toolchain; the pin comes from `lean-toolchain`.
   - **The cache:** narrowed to the Mathlib roots of the bootstrap set plus the open PR heads
     (355 roots, 3,605 files, from the Azure host `lakecache.blob.core.windows.net`, 0 failures).
     `mathlib4.lean-cache.cloud` is refused by the proxy, but this Mathlib uses it only under
     `USE_FRO_CACHE=1`. A new Mathlib import needs a narrowed fetch for its root.
   - **A worker restart ends every process**, detached ones included, and restarts came while the
     session waited on the user. Long jobs must be resumable: `bootstrap-snapshot.sh <wt> <name>
     --resume` continues a killed bootstrap after its checks. After a restart, check
     `$TCSLIB_SCRATCH/fills/replay/*.log` and resume.
   - **`lean_check_tree.sh` takes no lock slot**, so a running bootstrap or replay holds slot 2 by
     hand: `mkdir $TCSLIB_SCRATCH/locks/lean-slot-2 && echo <its bash pid> > …/pid` (freed by the
     stale check when it dies).
   - **ext4 has no copy-on-write:** `cp -R` copies a snapshot in full (about 1 GB). Prune.
   - `mkreplay.py` calls `$TCSLIB_SCRATCH/api/staticsorry.py`: a copy of
     `devtools/seyoon/staticsorry.py`. `$TCSLIB_SCRATCH/api/chain.py` lists a change's pre-replay
     compile chain.
   - **Sub-agents:** at most five at once, for independent tasks (WORKFLOW §5).
   - **PFR is left out** (ruled by the user, 2026-11-05: option B). The Mathlib cache does not
     provide the `PFR` package's oleans, so the twenty `CommunicationComplexity/NewmanTheorem`
     modules that import it (directly or not) are left out of cloud snapshots
     (`bootstrap_order.py`; `skipped-<name>.txt`). They are outside WORKFLOW §2's snapshot areas,
     and no open PR's replay reached them. Building them would need a direct `lean` run over 31
     PFR modules, which the rules do not cover: ask the user first.

The local Mac's snapshots (`oleans-*`) and review folders are not carried over. Every record the
gates cite is in the repository: packs, evidence, reviews, reports and deliveries' evidence.

## 2. State (updated 2026-11-05, about 10:40 PST): quiescent, no replay owed

**Merged on 2026-11-04/05:** #181 (space facts), #182 (ARM embedding), #184 (the codec's edge mode),
#189 (G5's statements; gate 92), #188 (E-D's landing, `exists_diagonalizer`; gate 93), #190 (the
configuration facts; gate 94, `replay-lcf3`).

| PR | What | Replay | Gate | Next |
|---|---|---|---|---|
| #191 | `11a3a562` | `replay-lnf7` **passed** | 95 **CLOSED** (round 5) | **merged** 2026-11-06 (`a1d7fea4`); H's brief next |
| #196 | the deepening's API: `SavitchARM/Window` (window exactness, termination) and eleven facts in eight files (design §9–§10; decisions 4 and 5) | `replay-ldwa` **passed** (73 modules from `oleans-lcf3`, at `89f4ebbc`; the existing 30 `sorry`s) | 96 **dispatched** 2026-11-05 (`outbox/gates/96-deepen-api-gate/`, 209 sections) | merge when gate 96 closes; then issue the deepening fill (Claude) |
| #197 | G5's consumer API (decision G5-F1, API first): `Build/ZoneStep` (`exists_zoneTrackStepTM`, the amortization), `Contract.zero`, `ZoneRebalance`'s equations | `replay-lzsa` **passed** (111 modules from `oleans-lcf3`, at `0a1b64d5`; the existing 45 `sorry`s) | 97 **staged** (`outbox/gates/97-zone-step-api-gate/`, 91 sections) | dispatch gate 97; merge when it closes; then G5's fill brief |

On #191's merged tree the nondeterministic time hierarchy is admission-free:
`ntime_hierarchy`, `ntime_hierarchy_of_pos` and `NTIME_linear_ssubset_square` rest on the
standard axioms (gate 95's `evidence/axioms/NTHAx.out`). With #191 merged, the headline count is
expected to reach **21 of 26**; the status record is `campaign/status/2026-11-05-headlines/`.

**Merging several of these:** each replay above chained from `oleans-lcf3` with only its own
PR. Once two or more have merged, the merged campaign's first snapshot (§1, item 4) is the replay
of record for the combination.

**Mac-only branches with commits not in the campaign** (checked 2026-11-05; none has an upstream
that contains them). Most are superseded deliveries or landings:
- `deliver/fill-eq-query-in`, `deliver/fill-s13d-g4-cont4-in`, `deliver/fill-u2s-universal-in`;
- `lean/g4-cont1-partial`, `lean/ntime-diag-bf`, `lean/seam-layout`;
- `local/eq-cp1-landing`, `local/eq-cp1-landing-v2`;
- `dedup/ch34-d4`, which has no Lean.

Two October re-points may still be 12.2c material. The user had them pushed as archive branches
(2026-11-05):
- `archive/mac/canon-mapcomp-repoint` (`e4c5d015`): `CodeSimulator`'s grammar-stage relabeling as
  `Cfg.mapState_mapState`;
- `archive/mac/r-leaf-repoint` (`89bf6acb`): `NDCodeSimulator`'s input rewinds as
  `Build/InputRewind`'s.

The rest stay on the Mac.

`maint/12.2c-t2a` (2026-10-12) is the T2a facade wiring.

**Update (2026-11-05, cloud session, about 14:30 PST).** The first cloud snapshot is
**`oleans-cloud0`**: 869 modules (the root's import closure less the 20 PFR modules), at
`dfed8b1f`'s Lean tree, `$TCSLIB_SCRATCH/fills/replay/bootstrap-oleans-cloud0.log`. Each PR's
replay below chained from it with only its own PR.

| PR | Head | Replay | Gate | Next |
|---|---|---|---|---|
| #191 | `b2bac06f` (round 3's repair `698dcdf5` + a records-only merge) | `replay-lnf5` **passed** (4 modules from `oleans-ldwa3`, 0 `sorry`) | 95 round 3 did not close (0/1/1: one more untyped re-derivation); round 4 **dispatched** 2026-11-06 (96 sections) | merge when it closes |
| #202 | `7b5774fb` | `replay-lsi2` **passed** (112 modules) | 98 **CLOSED** 2026-11-06 | **merged** 2026-11-06 (`8a505fc9`); `oleans-lsi2` is the campaign's snapshot; G5's brief after #207 |
| #207 | `d01332e4` | `replay-lzde2` **passed** | 99 **CLOSED** | **merged** 2026-11-06 (`d43a1374`); G5's fill brief issues |
| #208 | `d01c56a4` (round 1's `a074d9b7` + the round-1 repair `9db4f2ee`: F1's harvest `length_bits_succ_le` in `Machines/Bin`, and F2–F4; IL-1's six re-points `6a289c50`, both ruled by the user) | `replay-ldp6` **passed** (190 modules, from `oleans-lnth`; head `36ed2deb`) | 101 round 1 **HOLD** (0/1/3/3); round 2 **dispatched** 2026-11-06 (74 sections) | **merged** 2026-11-06 (`1bf65f3e`, the user); `replay-lcamp2` (the combined replay, 195 modules from `oleans-lnth`) **passed** (0 failed; `campaign/status/2026-11-06-campaign-replay-2/`) |
| #211 | `f239dafd` (G5's delivery `71046be0` + the landing edits `c00340d4`, `794ffb48`, `f239dafd`: the sweep's 15 hits, the review's N2/N4/F9, F6 through `SymbolLift` and F5 through `Contract.inPhase`; both imports ruled by the user) | `replay-lg8` **passed** (3 modules on the campaign after #217, 0 `sorry`) | 102 round 3 **dispatched** 2026-11-06 (cites #217/gate 108) | **merged** 2026-11-06 (`f743ee97`, the user); `two_work_tapes_run` proved, `universal_TlogT` admission-free; **`oleans-lcamp5`** (= `oleans-lg8`) is the campaign's snapshot |
| #212 | `034e72e3` (ZP-1: `ZoneRebalance`'s twelve inline steps cite `zoneRowPre_mapState_iff`) | `replay-lzp1` **passed** (5 modules from `oleans-lnth`) | 103 **dispatched** 2026-11-06 | **merged** 2026-11-06 (`4eb0f801`, the user); `replay-lcamp2` (the combined replay, 195 modules from `oleans-lnth`) **passed** (0 failed; `campaign/status/2026-11-06-campaign-replay-2/`) |
| #213 | `fdc0e425` (CE-1: BPLInP's public copy deleted, five uses cite `ExpBFS.coreSum_eq_of_code_eq`) | `replay-lce1` **passed** (7 modules) | 104 **dispatched** 2026-11-06 | **merged** 2026-11-06 (`a28b8c42`, the user); `replay-lcamp2` (the combined replay, 195 modules from `oleans-lnth`) **passed** (0 failed; `campaign/status/2026-11-06-campaign-replay-2/`) |
| #214 | `fa1673aa` (AS-1, all of it: 173 in-scope declarations over 40 files; the 48 of round 1 plus `acde1f4e`…`fa1673aa`, 130 more and 3 caveat branches, 501 sites; PathHard's `stp` macro no longer unfolds `astep`) | `replay-las2` **passed** (109/0, after #216) | 105 **CLOSED** (round 3 PASS 0/0/1; AS-2 and MT-1 acknowledged by the user) | **merged** 2026-11-06 (`9df4a7bd`, the user) |
| #215 | `57939a97`+ (SG-1: `CounterLoop`'s `counterSpan` through `Segment`) | `replay-lsg1` running | gate 106 after the replay | — |
| #216 | `485cfbab` (RP-1, widened: 23 public bodies in 14 files read #196's seven definitions through their equations; `cl_iff`'s sketch `3d0f6ceb`) | `replay-lrp3` **passed** (53 modules from `oleans-lcamp2`) | 107 **CLOSED** 2026-11-06 (PASS 0/0/2, evidence corrections) | **merged** 2026-11-06 (`e4e7a419`, the user); its Lean equals `485cfbab`; `replay-lcamp3` (its 53-module closure from `oleans-lcamp2`) builds the new campaign snapshot `oleans-lcamp3`; then WL-1 and CQ-1 |
| #217 | `fc8d9093` (NZ-1: `NDTM.not_haltsWithin_zero`; 8 sites, both readings, incl. `ExpectedTime`'s probability form `51006620`) | `replay-lnz2` **passed** (261 modules from `oleans-lcamp3`, after #216) | 108 **CLOSED** (PASS 0/0/2); gate 102 r3 **CLOSED** (PASS 0/0/1) | **merged** 2026-11-06 (`eb8cbf60`, the user); its Lean equals `fc8d9093`, so `oleans-lnz2` is renamed **`oleans-lcamp4`, the campaign's snapshot**; NZ-1 retired |
| #218 | `2d65a899` (B6's H landing: `space_hierarchy`, `LOGSPACE_ssubset_PSPACE` proved; `SPACE_linear_ne_NP` escalated as E-PAD; the sweep's 35 sites and the review's text fixes) | `replay-lh3` **passed** (2/0 on the campaign after #211; head `118e3d50`) | 109 **CLOSED** (PASS 0/0/4; minor 1 fixed `1a782c36`) | **merged** 2026-11-06 (`d70949ff`, the user) |
| #219 | `cf4dd831` (E-PAD statements: new `SpaceComplexity/Padding`, `padLang`, `mem_padLang_iff`, `mem_SPACE_padLang` sorried; facade Contents `130b91c3`) | `replay-lep3` **passed** (2/0 on the campaign after #211) | 110 **CLOSED** (PASS 0/0/1) | **merged** 2026-11-06 (`7027dead`, the user) |
| #223 | `lean/thm31-book` at `a08d70d9`, on #211's branch (`time_hierarchy_log`, `time_hierarchy_book`, `time_hierarchy_book_of_pos` proved on the standard axioms; `twoTapeSelfSimulator` from `exists_selfUniversalK 2`; evidence `campaign/items/t31/`; rule 10: `DTIME`/`DecidesInTime` read directly in `normalForm`, as `oneTapeSelfSimulator` does, no published equations) | `replay-lt32` **passed** (14/0 on the campaign after #218/#219) | 113 **CLOSED** (PASS 0/0/4; fixes `09a10335`, regenerated seal) | **merged** 2026-11-06 (`72fcfbef`, the user) |
| (U2H) | `lean/u2-harvest-api` at `db12c154`: the U2 harvest API (F6's prerequisite). New `Build/UniversalParts` (976 lines, 22 public rows, both generalizations proved); `UniversalK` 2,873 → 2,127 lines, statements byte-identical; evidence `campaign/items/u2harvest/`. **RS-1 ruled (the user, 2026-11-06): publish the restart identity in UniversalParts** (`Turing.MultiTapeTM.initCfg_eq_mapState`) | replay after `replay-lcamp3` | 112 **dispatched** 2026-11-06 (37 sections) | **#221** opened; `replay-lhv1` **passed** (5 modules, after #216) |
| #222 | `345c6371` (NatBits: BL-1, NB-1, LS-3; new `TuringMachine/NatBits`; 21 sites + Meyer×2; `Frag` cherry-pick of #215's) | replay after #217 merges (about 340 modules) | dedup gate after the replay | — |
| #209 | `0b05cc3a` | `replay-lnth` **passed** | 100 **CLOSED** | **merged** 2026-11-06 (`5761d6e0`); `oleans-lnth` is the campaign's snapshot |
**Snapshot (2026-11-06, after #214, #223):** `replay-lcamp7` (120 modules from `oleans-lcamp6`) running → `oleans-lcamp7`; then #220, #221, #215, #222 re-replay on it. **After #218, #219:** `replay-lcamp6` (3 modules from `oleans-lcamp5`) running → `oleans-lcamp6`. **After #211:** **`oleans-lcamp5`** (= `oleans-lg8`, Lean `f743ee97`). **After #217:** `oleans-lcamp4` (= `oleans-lnz2`, Lean `eb8cbf60`). **Before, after #216:** `oleans-lcamp3` (Lean `e4e7a419`; `replay-lcamp3`, #216's 53-module closure from `oleans-lcamp2`, **passed**, `campaign/status/2026-11-06-campaign-replay-3/`; `oleans-lcamp2` deleted). Merged-tree replays on it are queued for #214, #215, #217, #218, #219, #220 and #221. **Earlier:** **`oleans-lcamp2` was the campaign's snapshot** (Lean `a28b8c42`, after #208, #212, #213). `oleans-lnth`, `oleans-cloud0`, `oleans-lg7` and `oleans-lrp2` are deleted (disk). Chained from it: `oleans-lrp3` (#216, 53 modules, **passed**), `oleans-lsg2` (#215), `oleans-lnz1` (#217), `oleans-lh1` (#218).
| #196 | `ce9d63f4` (the repair `b1b5199b` + a records-only merge) | `replay-ldwa2` **passed** (73 modules, the existing 30 `sorry`s) | 96 **closed** (round 2 PASS 0/0/1); `replay-ldwa3` on the merged tree **passed** | **merged** 2026-11-05 (`bdc73ab1`); the deepening fill (Claude) next |
| #197 | `fde50a5a` (the closing commit `20e7fc75` + a records-only merge) | `replay-lzsa2` **passed** (111 modules, the existing 45 `sorry`s) | 97 **closed** (PASS 0/0/6, the minors swept) | **merged** 2026-11-05 (`33ceeed1`); G5's fill brief next |

**After #197's and #196's merges** the campaign's Lean tree is #196's head's (`97adec69`), and
`oleans-ldwa3` is its snapshot (chained `oleans-cloud0` → `oleans-lzsa2` → `oleans-ldwa3`). Every
open PR's replay chains from it on the merged tree.

**#202** (`Segment.iterate_seq`, G5's iteration; the user's ruling API first): gate 98, above.

**The deepening fill is issued** (2026-11-05; agent Claude): `campaign/fills/ch34/briefs/ch34-fill-deepen.md`
at `a89e8d70`, ancestor `fd97df61`, with the addendum v2.6; **dispatched 2026-11-06** (the user).
Its pre-ship ran on the merged tree (`campaign/fills/ch34/logs/ch34-fill-deepen-preship.log`).

**Snapshots on the cloud VM:** `oleans-cloud0`, `oleans-ldwa3` (the campaign's), `oleans-lsi2`
(#202's merged tree, **the campaign's since #202 merged**), `oleans-lnf7` (#191 on it), `oleans-lzde2` (#207 on it) and `oleans-ldp` (#208's delivery). #191 and #207 merged 2026-11-06 (`a1d7fea4`, `d43a1374`); `replay-lcamp1` (both closures, 9 modules, from `oleans-lsi2`) **passed** (0 failed; `TwoTapes`' one `sorry`; `campaign/status/2026-11-06-campaign-replay/`): **`oleans-lcamp1` is the campaign's snapshot** (Lean `d43a1374`). Kept on the VM: `oleans-cloud0`, `oleans-lcamp1`, `oleans-ldp2` (#208), `oleans-lnth` (#209). Once #191 or #202 merges, its snapshot is the
campaign's; delete the other when both have merged and a combined replay has passed.

**G5's fill brief** issues after #202 merges. Its route probe (the frame through
`alphabet_reduction_run`, and `k = 0` through R1) is proved (`campaign/fills/u2s/drafts/u2s-fill-g5/route/`).

**The user's rulings (2026-11-05):** gate 95 F1 repair; gate 96 F2 harvest; WS-1 acknowledged by
kind and widened; QL-X1 an idiom and CQ-1 opened; gate 97 F5 publish; CE-1 acknowledged; PFR left
out of cloud snapshots. All are in `duplication-ledger.md` and the gates' `resolutions.md`.

**Duplication rulings of 2026-11-05 (the user)**, recorded in `duplication-ledger.md`:
- **WS-1**, acknowledged by kind and then **widened**: every proof that one step keeps a
  configuration within a window of any shape, and window monotonicity; canonical
  `Cfg.InWindow.apply_iff`, `Cfg.InWindow.mono`, and the tape half (to be published in 12.2c;
  `Oracle`'s private `apply_workTapes_eq_of_ne` is its source).
- **CE-1**, acknowledged for 12.2c: `coreSum_eq_of_code_eq`, public in both `ExpBFS/Radius` and
  `Randomized/BPLInPCount`.
- **QL-X1**: the `NoEdge`/`Rel` pair is an idiom; **CQ-1** opened (codec-level query predicates).
- **ZP-1**: `zoneRowPre_congr` and `zoneRowPre_mapState_iff` published; `ZoneRebalance`'s twelve
  inline sites re-pointed in 12.2c.
- Maintainer records with them: RN-1 accounting (`nf_pack`), RC-4 (F8's row candidates), WL-1,
  WC-1 (optional), RP-1 (definitional reads #196's equations can replace).

## 3. Queue after the PRs

1. **The deepening fill** is dispatched (2026-11-06, Claude): `campaign/fills/ch34/briefs/ch34-fill-deepen.md`.
   Its delivery is reviewed by a sub-agent, then landed by PR and a fill gate.
2. **G5's fill brief is issued** (2026-11-06, agent Claude): `campaign/fills/u2s/briefs/u2s-fill-g5.md`
   at `fe5cb6fb`, ancestor `335d31d4`, staged in the exchange's `outbox/fills/u2s-fill-g5/`;
   **dispatched 2026-11-06** (the user).
3. **B6's H, the space hierarchy** (`space_hierarchy`, `LOGSPACE_ssubset_PSPACE`,
   `SPACE_linear_ne_NP`; agent Codex): **issued 2026-11-06**, `campaign/fills/b6/briefs/b6-fill-hierarchy.md`
   (base `e6bc1968`; inputs `campaign/fills/b6/inputs/b6-fill-hierarchy/`, the 43-file screen base,
   pre-ship log), after the review (`drafts/b6-fill-hierarchy/review-2026-11-06/`: 1 blocker,
   5 majors, folded in). Staged on the exchange (`outbox/fills/b6-fill-hierarchy/`, `c618ae35`);
   **dispatched 2026-11-06** (the user). **Delivered 2026-11-06** (`fill-b6-hierarchy.zip`, SHA-256
   `9c3817bc…`, final commit `30222bbd`, `deliver/fill-b6-hierarchy-in`): `space_hierarchy` and
   `LOGSPACE_ssubset_PSPACE` proved; `SPACE_linear_ne_NP` ends in the permitted escalation
   **E-PAD** (an exact padded-language linear-space decider); REPORT at
   `campaign/fills/b6/reports/hierarchy-REPORT.md`. Review, sweep and landing next. **Ruled (the user,
   2026-11-06):** `SPACE_linear_ne_NP` stays H's last checkpoint and may end in a named escalation
   (no published host for the padded decider or the padding map's polynomial time). (The other "H",
   `campaign/fills/h/`, the nondeterministic time hierarchy, landed as #172; with NF and E-D
   merged it rests on the standard axioms; #209 corrects its module's Status paragraph.)
4. **The dedup window (12.2c)** — **started 2026-11-06 (the user): small, separate dedup PRs, one
   family each, the mechanical ones first, each with a replay and a gate pack staged for the
   user to dispatch.** **Ruled (the user, 2026-11-06):** RO-1's `MultiTapeTM.runFrom_one` lives
   in `TuringMachine/CfgFacts`; BL-1 and NB-1 share a new `TuringMachine/NatBits` module (below
   `Encoding` and `Machines/Bin`; `CircuitComplexity` excluded); mechanical re-points in Hydroxyi's
   files are allowed with an FYI line in each PR, while CL-1, CQ-1 and WL-1 (interface design)
   wait for Hydroxyi. **Ruled (the user, 2026-11-06, second round):** SG-1's two imports of
   `Build/Contract/Basic` allowed (`Tautology`, `SingleTape`); RO-1: replace `EmitIterEmbed`'s
   Bool-only `Turing.runFrom_one` by the general lemma and re-point **every** site, colleague-owned
   files included; NZ-1 acknowledged, publish `NDTM.not_haltsWithin_zero` and re-point now;
   mechanical dedup edits in colleague-owned files (`CircuitComplexity/`, Meyer) allowed in every
   family, with an FYI line (no renames or design changes there without asking); NatBits: the
   plan's defaults D1–D6 accepted, one PR after #208 merges, D9's families recorded for later.
   **Ruled (the user, 2026-11-06, Hydroxyi not active):** CL-1 the full refactor (one public
   membership lemma for encoded triples and one decider wrapper parameterized by the mode's tail,
   the five languages re-proved through them); CQ-1 a `def` per query with its `_iff` in
   `Codec/Langs`, `ISGen.InitM`/`AccM` deleted and re-pointed; WL-1 moved beside `WalkLe` in
   `PathWalk` as `Complexity.walkLe_succ_iff`, after #216 merges.
   **Next roadmap tracks, all three in parallel:** F6 (U2's harvest, then the fill), the book-form
   Thm 3.1 statement phase, and Ladner's statement phase (plan: `campaign/items/roadmap3/PLAN.md`). **Ruled (the user, 2026-11-06, on the plan's §(e)):** (1) the U2 harvest's rows go in a **new `Build/` module** (not in place in `UniversalK`), harvest before RO-1's `UniversalK` edits (RO-1 then re-points the published row); (2) in `Hierarchy.lean`, after H lands, **E-PAD's continuation of `SPACE_linear_ne_NP` first**, F6's fill after; (3) book-form Thm 3.1 lands **after #211 merges**, admission-free, **with** `time_hierarchy_book_of_pos`; (4) Ladner: **LD-1 to LD-7 as recommended**; LD-8 (Exercise 3.6's parts against the book) is the maintainer's check before docstrings. Still open: D-F6-3 (F6's startup route), to decide after the harvest's consumer probe. **CL-1 (the user, 2026-11-06):** add `mem_validLang_iff`, `mem_initLang_iff`, `mem_acceptLang_iff`, `mem_stepLang_iff` (`Iff.rfl`, beside `mem_edgeLang_iff`); one `mem_codeLang_iff` with a generic injective tail; `stepLang_mem` stays outside the wrapper (`campaign/items/dedup/cl1-SCOPE.md`). **Progress:** ZP-1 is #212 (gate 103). **RO-1 is parked** on
   `lean/dedup-ro1` (`7c940a8a`, no PR): its scope is about 200 sites and a public Bool-only
   `Turing.runFrom_one` already exists; two questions for the user in the ledger's RO-1 entry.
   NZ-1 is #217 (acknowledged; it also carries gate 102 r2's two majors). CE-1 is #213 (gate 104), AS-1 #214 (its in-scope member; five in
   `CircuitComplexity` await the owner), SG-1 #215 (`CounterLoop`; `Tautology` and `SingleTape`
   await an import ruling), RP-1 widened (in progress). **NatBits (BL-1, NB-1) is planned, not
   started:** `campaign/items/dedup/natbits-PLAN.md` (one PR, 18 files, a 340-module replay; after
   #208), with decisions D1–D9 for the user. The families: the ledger's acknowledged families, among them LS-1, LS-3, BL-1
   (scoped by kind), CL-1, AS-1, RC-1–3, QF-1 and NF-X1; since 2026-11-05 also WS-1 (scoped by
   kind and widened; publish the tape half first), RC-4, CE-1, ZP-1, CQ-1, WL-1, RP-1, SG-1 (2026-11-06) and WC-1
   (optional), with QL-X1 an idiom exclusion.
5. **The deferred cleanup of public-facing docstrings** (WORKFLOW §2): about 280 campaign labels in
   existing Lean text, and E-D's frozen proof sketch (F9).
