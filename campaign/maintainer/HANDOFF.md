# Arora–Barak ch. 3–4 maintainer handoff

Ruled by the user on 2026-11-04: the campaign moves to a cloud machine like the Pass–Shelat line,
with the exchange in the `arora-barak-ch3-4/` folder of the orphan branch
`exchange/pass-shelat-ch5-8`. The handoff point is **quiescent**: the heavy local replays finish
on the Mac first. Read `WORKFLOW.md` (beside this file) first; it holds the standing rules. The
long-form state is in `campaign/backlog.md`, and the duplication debt in
`campaign/duplication-ledger.md`.

## 0. Current state (2026-11-08T17:46:20.116153+00:00; authoritative)

Seyoon merged #233, authorized overnight preparation while keeping mathematical holes
for fills, and selected **Codex for all morning audits**. On returning, Seyoon confirmed
dispatch of the seven prompts already sent. Root builds/reviews/publishes; Seyoon alone
dispatches external agents, rules on design/debt and merges. Every source PR below is
**Not yet clear to merge**; dispatch and internal peer review do not close an external gate.

Campaign Lean remains `9b5dcf46408db681bcbc721930ef2203fa6bc47d` / **whole MAC8**:895 objects and1003 tracked Lean blobs.
All subsequent campaign pushes are records only. #215/#222/#223/#228/#229/#230/#233/#234/#235
are merged; the eight overnight source PRs remain unmerged. Next free gate:**129**.
All own Lean and copy-screen jobs are complete. No mathematical fill was self-dispatched.

### Eight current source PRs

| PR | Gate | Pushed source HEAD | Checks and current status |
|---|---:|---|---|
| #241 |121|`d64dff4fbef865d815c6a561ce8037ea1bae07a2`|9 first-entry proofs;157/static0/35,50 selected types exact,22pairs;33screen8new5gone/all13dispositioned; Dispatched; Codex findings pending |
| #242 |122|`f3c8c050ef98375bc237c72bde74f83d33833374`|10 first-halt +3 mandatory backwards-live proofs;222→153/static0/31,13types,23heads/46pairs;44screen0new19gone4scores/all23reviewed; Final publication binding in progress |
| #243 |123|`7c4b1a3e15b800cc4a98624f71a3b27458a41340`|5 public run-law forwards;80/static0/31,12pairs;33screen0new2gone; Dispatched; Codex findings pending |
| #244 |124|`cfa6a3ee327b03e601b25fd5f0535e85fd18f897`|3 SafeRun closures +1 private bridge;80/static0/31,14pairs;33screen0new0gone; Dispatched; Codex findings pending |
| #245 |125|`b8bb1f194b86c1b0c1d56e6c3f57e1defec37e80`|2 Hardness head/tail forwards;26/static0/0,30pairs;33screen0new10gone; Dispatched; Codex findings pending |
| #246 |126|`48d715acefaa9eb1c6b1ffc8656fb79cc0ab1b10`|1 local hinit reader;18/static0/0,6pairs scoped to hinit;33screen0new1gone; Dispatched; Codex findings pending |
| #247 |127|`e16049ad20823b3e6abba171e328489746062080`|2 existing readers in1 private proof;23/static0/0,full target6pairs;48screen0new0gone0scores; Dispatched; Codex findings pending |
| #249 |128|`1096e50b4e105392737ec52939b1db0cdbd9316d`|17 approved Ladner declarations/6mathholes;2/static0/6,895→896,18pairs/6edges;49screen0new0gone0scores; Dispatched; Codex findings pending |

The source scopes remain separate family PRs. WORKFLOW§3 required the three mechanical
backwards-live companions in #242's already touched owners; their statements/imports/definitions
remain exact. Only actual gate closures and merges retire implementations. All admission,
metadata, full-proof/limited-prefix and prior-execution transport bounds remain in each pack.

### Morning dispatches and immutable bindings

`campaign/status/2026-11-08-overnight/DISPATCH.md` is the complete current prompt index.
Each gate’s publication.json/prompt.md records every exact source/records/exchange/bundle
pin, SHA/section count and user dispatch confirmation. Immutable exchange READMEs record
publication-time status; these records show subsequent dispatches.

- Gate121: 817sections/SHA`12bbc82fc917ea24b73dab33d6351c897618a09111ee5595d692283bfa7ed821`; dispatch confirmed; findings pending.
- Gate123: 373sections/SHA`057363ca1d75034d026280cadc56350d0ebbf89f59144b4a94c72e552e070fb0`; dispatch confirmed; findings pending.
- Gate124: 670sections/SHA`79ca4ad99603e960e8eca889c637779b88e955991aa3a50f3e7f5efe97011f5e`; dispatch confirmed; findings pending.
- Gate125: 291sections/SHA`431f8d4119cc69b4554308ed17575b434f73f3d4216be44d4db83f534556ede5`; dispatch confirmed; findings pending.
- Gate126: 261sections/SHA`8b8ae13401e9af863bc2decdbac810283657def59e269e8caf52df4f2be0bd0c`; dispatch confirmed; findings pending.
- Gate127: 615sections/SHA`acf98cfe3e58d5122487ab7fb6a64efde25a07b308cae98a623c687789f8633a`; dispatch confirmed; findings pending.
- Gate128: 885sections/SHA`57b721338a51be0ab7d08e078163a0151bde3a232a3c962d99298153fadd7a78`; dispatch confirmed; findings pending.

The earlier gate121816-section prompt is **VOID**; use its817-section replacement.
The old gate123359-section prompt is **VOID**; use373/SHA057363. Intermediate unissued
123SHA607f and125SHAb526 are superseded history. No source/evidence execution was changed
by the121 record fix. The58 exact data captures are committed; the original FE archives
already preserved all50 affected FE files. Independent correction review and root’s
3895/3895 committed-blob recheck are under record-completeness-review/.

### Passed prospective merged-tree chain

The complete actual evidence lives in joint-chain/RECEIPT.json: all module logs/source
captures, source/object maps, unchanged complete inputs, local commit bytes/tree listings
and physical output verification. Every snapshot is a whole overlay; no composition.

- njoint1:local`50998b88fda9f5c9ae949735b70bc4c14b3a19fe`, actual257PASS/static0/45, output895.
- njoint2:local`651c031dc8b571393ed54efff36b96245277a192`, actual23PASS/static0/0, output895.
- njoint3:local`a3424c8d1469b4375d76b9b99b67cd34fe447d66`, actual2PASS/static0/6, output896.
- njoint4:local`eb7c317ee9a5f947c3cf22e8f1f66529015f87d2`, actual153PASS/static0/31, output895.
- njoint5:local`b9e76f4c9db3049e6e56b838715aedc945abd258`, actual154PASS/static0/37, output896.

Final seven-cleanup lineage:MAC8→NJ1→NJ2→NJ4. Final all-eight lineage adds NJ3 after NJ2
and NJ5 after NJ3. NJ4 does not consume NJ3. NJ1 precedes the final Nat reader; NJ2/NJ3
precede the final FH13 companions. NJ4/NJ5 validate all final heads. Their local validation
merges are not campaign merges. Do not adopt a campaign baseline until Seyoon’s actual
merged Lean blobs equal a passed tree. NJ2’s stale raw header label has a preserved erratum;
its request/all895 input hashes correctly identify the entire NJ1 predecessor.

### Ladner, held fronts and continuation

The approved Ladner design note precedes source. Four definitions and six readings are
standard-axiom-only; six direct mathematical holes and the dependent ladner packaging retain
sorryAx (7 selected closures,6 direct holes). No mathematical completion or fill readiness
is claimed. The exact owner/115-import source/object transport supports the older actual
metadata/guard/edge runs; current2-module replay is separately actual1096. TCSlib9-head guards,
all17 seeded roots and encountered-theorem proof boundaries are explicit. Source attribution
uses the approved Theorem3.3/proof fallback; exact2009 exercise-part wording remains unverified.

Three user questions remain pending; no approval is inferred from the overnight mandate:

- SAT's PolyTimeBlockLoop import for head/tail leaves: complete held proposal under
  campaign/items/dedup/sat-word-proposal/.
- SAT_exists_linear_verifier: complete sharp n+1 owner/consumer proposal under
  campaign/items/ladner/sat-linear-verifier-proposal/. It blocks the identified fill route,
  not the already prepared statement skeleton. Numeric simulator and concrete memo/FP
  bounds also remain fill obligations; no new public host route is approved.
- RO1's generic runFrom_one home revision CfgFacts→Deterministic: both complete options
  under campaign/items/dedup/overnight-2026-11-08/review/ro1-*-option/. API/all-sites scope
  was approved, but the home/import revision is not. CfgFacts has the demonstrated cycle;
  alternate7 owners checked/54 not recompiled. Preserve the intentionally dirty old candidate.

A bounded continuation triage records42 dispositions/25 source bindings at final-eight
source. Exact matches are already in these PRs; remaining inspected targets need reader,
design or mathematical work. This is not a whole-library absence/debt-completion claim.
Seven held FH targets remain restored across six complete BASE-exact owners. Wider accepted
debt retains its exact kinds/owner/window, after MIG1 and before further SAT/Hardness fills.

Next: finish any still-pending publication, then review returned Codex findings with
parallel subagents. Preserve reports verbatim, apply mechanical fixes, pause new design
questions, and issue **Clear to merge** only after external closure and current-tree
replay/validity checks. No new fill dispatch is authorized by an audit result.

### Machine and preservation constraints

Local3/machine5 Lean slots, nice10/j4; only leanelab/leanelab-o, never lake build.
One global screen lock. Every shell sources scratch/env.sh; Python only-I. Use whole APFS
snapshot clones and unlink compiled outputs before elaboration. Current own jobs:none.

R is /Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4;S is the original
tcslib-scratch. S/wt-hk→R;wt-xch→shared exchange;wt-camp→ab34-campaign-current;
wt-restart-reader→ab34-campaign;wt-night-joint→ab34-overnight-joint;
wt-night-all8→ab34-overnight-all8;wt-ladner-statements→ab34-ladner-statements.
Keep every PR worktree's package link. Records direct with fetch/rebase; exchange only
our AB subtree and pull/rebase before each push; no force. Preserve unrelated exchange
untracked files, R's preexisting118 static folder and the held RO1 source worktree.
Main’s untracked3sumapsp_example.lean stays SHA256
`14eb21e97204139a6ca3080245a40547002de3e9e870b8d35d0f5ef60c016a84`.
Original section0 is preserved in campaign/maintainer/history/.

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
