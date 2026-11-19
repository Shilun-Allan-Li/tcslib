# EF-H11 `ef-h11-sharing-bgw` · final r1 · landing

**Landing branch pushed: `land/ef-h11-sharing-bgw` at `11ea959f183d3ce7feaa6d2b8204446608c1ca92`.**

- **Base:** the current `iO/phase-a-base`, `5382668bc9cc496355c83e7b77909d9647e089b3`. It already carries
  #384's DL-66 promotion of `samplesEfficiently_comap`.
- **Commits:** the six worker commits and four signed maintainer commits: LE-h11-w1, LE-h11-w2,
  LE-h11-promote and LE-h11-doc.
- **Rulings applied** (decision-log rows of 2026-11-18/19):
  - EF-H11-R1, settled by EF-W1-R (A): LE-h11-w1;
  - R2 (A): LE-h11-w2;
  - R4 (A): LE-h11-doc;
  - R5 (A), ledger DL-66 to DL-68, with DL-66 now executed on #384: LE-h11-promote.
- **Not in this landing:** R3 (A) and R6 (A) are separate follow-up items. DL-63 is a note only (see *Notes*).
- **No PR is open.** Seyoon opens it as a draft; the body below is ready to use.

Run on 2026-11-19, 03:35–04:10 UTC. `$SP` is
`/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`, and the work is in
`$SP/land-efh11/`.

## Inputs

- **Delivery.** `inbox/fills/ef-h11-sharing-bgw/` at exchange commit `4e787bc232b256f53d0acfd17794f908e24afc1e`.
  - Its tree is `1a0d3be3…`, the same as at the exchange tip `8f15c31d`; no later commit touches the path.
  - It was extracted with `git archive`. The top `SHA256SUMS` and `evidence/SHA256SUMS` both verify (0 failures).
- **Evidence zip.** `ef-h11-final-r1-evidence.zip` has SHA-256 `a8814b70…`, matching `evidence-SHA256SUMS`. Its
  inner `SHA256SUMS` verifies.
- **Scope-request patches** (`evidence/scope-requests/`): `W1-defs-readers.patch`,
  `W1-efficient-after-readers.diff`, `W2-readers.patch` and `W2-bgw-mul-agreement.diff`.
- **Records tip.** `cryptography/pass-shelat-ch2-4` at `53e430b6`, with `TCSlib` tree `745bf4b4`. That is
  `bff0567b` plus U12/U13: only `GSW/Branching` and `GSW/DecryptFormula` differ.

## Commits

| # | Landing commit | Worker commit | Subject |
|---|---|---|---|
| 1 | `71acf81c9be540fdfbb6826c96a46a3f0a119abc` | `56ade728` | EF-H11: efficient secret-sharing interface and Shamir instance |
| 2 | `053f16ff614d7dbbfadef38cc8ee52c5c68d098b` | `145f998a` | EF-H11: BGW efficient resharer and per-party gate steps |
| 3 | `f71903045414c831e9a0f6ce6d3844e6d9bdc27c` | `dbf9319f` | EF-H11: read encWords [] through encWords_nil (Rule 10) |
| 4 | `a71f6ef32aa0f576ace487fc4b58fbefe0bae525` | `3045b0a0` | EF-H11: readers partyEmb_apply and coinModulus_eq |
| 5 | `ae444a22dec8fdab650109111481050783a1f5cd` | `9fefdd3c` | EF-H11: rename the dealer's power loop to dealerPowStep |
| 6 | `eebf2d3598ed908edb05f0d679ed5df6b7a5b22a` | `edacd3c9` | EF-H11: cite only the brief's anchors in DealerSamples |
| 7 | `a5a4ef90a526ce7c759a9216551c1d2fe622893b` | (maintainer) | LE-h11-w1: `Iff.rfl` readers for `Correct`, `LocalReconstruct`, `PerfectPrivacy` |
| 8 | `e92e943712056faa3e8daedc2fed14f983287200` | (maintainer) | LE-h11-w2: close the multiplication gate against `bgwEval_mul` |
| 9 | `89380ebe259de096297fc26f2efd0d388f5332e3` | (maintainer) | LE-h11-promote: use the promoted `CoinSampling.samplesEfficiently_comap` |
| 10 | `11ea959f183d3ce7feaa6d2b8204446608c1ca92` | (maintainer) | LE-h11-doc: Glue notes and reader formulas in docstrings |

- **Commits 1–6** come from `git am -3 -S` of the six delivered patches on `5382668b`.
  - Author name, email, date and message are identical to the worker's commits, and every patch-id matches.
    The worker's own `Claude-Session` trailer is kept (I7).
  - The tree after commit 6 is `074aa12b…`. That equals `git merge-tree --write-tree edacd3c9 5382668b`, so the
    result is the delivery on the new base.
  - The five files are byte-identical to the delivered `src/` (`ad53c9ab…`, `374b82fd…`, `0facb22c…`, and the two
    facades).
  - The base change does not touch these files. The worker's local `SecretSharing.samplesEfficiently_comap`
    does not clash with the promoted `CoinSampling.samplesEfficiently_comap`, because the namespaces differ.
- **Commits 7–10** are staged by explicit path. Each message ends with exactly the two required trailer lines.
- **All ten commits are SSH-signed**, with one `gpgsig` each.
- **Branch diff against the base:** 8 files, +1,811/−0. The tree is `43970005…`.

## Landing edits

- **LE-h11-w1** (F01, EF-H11-R1 by EF-W1-R (A)). This is the worker's W1 patch verbatim:
  - three `Iff.rfl` readers beside the definitions in `SecretSharing/Defs.lean`: `Scheme.correct_iff`,
    `Scheme.localReconstruct_iff` and `Scheme.perfectPrivacy_iff`;
  - the 6-line rewrite of the four transfer proofs in `SecretSharing/Efficient.lean`;
  - +21/−6 in total. The `+`/`−` lines are identical to phase 2's LE variant for these two files.
- **LE-h11-w2** (F02, R2 (A)):
  - `degreeReduce_apply` in `MPC/BGW/Protocol.lean`, `rfl`;
  - `recombine_eq_sum` in `SecretSharing/Sharing.lean`, `rfl`. It is the worker's `recombine_eq`, renamed.
  - `recombineRaw_bgwEval_mul` in `MPC/BGW/Efficient.lean`. Its "(Scope-request probe)" label is replaced by a
    statement docstring with `[BGW88, §3], [AL17, §3–4]` and a proof sketch. Its proof is the worker's, with
    `recombine_eq` renamed to `recombine_eq_sum`.
  - The two readers carry "Glue." docstrings with their formulas, instead of the worker's bare "The defining
    equation of `X`.".
  - The module docstring's scope note and `recombineRaw_reshare`'s docstring now point to
    `recombineRaw_bgwEval_mul`, and *Main results* lists it.
  - +36/−8 in total.
- **LE-h11-promote** (F05, R5 (A), DL-66 executed on #384):
  - The local `SecretSharing.samplesEfficiently_comap` and its *Main results* bullet are deleted from
    `SecretSharing/Efficient.lean`.
  - `dealerSamples_shamir` (`ShamirEfficient.lean`) now calls `Cryptography.CoinSampling.samplesEfficiently_comap`,
    and its docstring names it.
  - The deleted statement equals `CoinSampling.samplesEfficiently_comap`'s, modulo the `CoinSampling.` prefix
    (decls2 text).
  - Proof and docstring change only: +3/−19.
- **LE-h11-doc** (F04, R4 (A)), docstrings only: +119/−96 in the three new files.
  - **"Glue." notes for 86 declarations.** It goes in the statement paragraph, ahead of any proof sketch.
  - **The 10 bare readers** now state their formula, or describe it with "(formula: the body of `X` above)"
    for the long machine bodies, and carry "Glue.". They are `dealerSamples_iff`, `shareStep_eq`,
    `shareState_eq`, `shareRaw_eq`, `lagStep_eq`, `lagTerm_eq`, `recStep_eq`, `recombineRaw_eq`,
    `dealerPowStep_eq` and `dealerWord_eq`.
  - **Code unchanged:** the code of each file with comments removed is identical before and after.
  - **Hygiene:** the review's `hygiene.py` now reports **0** declarations without a source tag or Glue note
    (was 96). The two known structure-instance NO-SKETCH notes (`EfficientScheme`, `shamirEfficient`) remain,
    as accepted in review.
  - **Sizes:** widths ≤ 100; `ShamirEfficient.lean` is 984 lines.

## Re-check on the landing head

The re-check followed phase 2's recipe: the `snapshots.md` job recipe and the tools in
`olean-advance-a6d01b1b/tools-used/`, all run with `python3 -I`. There was no `lake build` and no cache get.

- **Scratch check head** (never pushed). A sparse detached worktree at `11ea959f` was merged with the records
  tip `53e430b6` (`--no-ff`, unsigned).
  - The result is `099b0f8d613e39122298de7cfe4240fe6ba8c914`, tree `b999ff3b…`.
  - That tree equals `git merge-tree --write-tree 11ea959f 53e430b6`.
- **Olean tree.**
  - `$SP/olean-replay-efh11-le` (phase 2's LE variant, `a299c19e`) was state-checked first: 1470/1470
    RESULT OK, with no file newer than its state. It was the closest match, since it already holds the verbatim
    W1 `Defs` and `Shamir`.
  - It was copied with `cp -al` to `$SP/land-efh11/replay`: 1,502 files, all hard links, plus 3,346 Mathlib
    symlinks.
  - Snapshot #11 `snapmap verify` gave 0/0/0, RESULT OK, before the run and at the end.
- **Plan.** `fullorder` at `099b0f8d` gives 1470 modules, the same set as phase 2's. `stateplan plan` gives
  **25 to build and 1445 reused**:
  - the iO-base delta: `CoinSampling/Efficiency`, `Contract` and the `CoinSampling` facade;
  - the EF-H11 owners and their downstream: `SecretSharing/{Efficient, Sharing, ShamirEfficient, Vector}`,
    `SecretSharing`, `MPC/BGW/{Protocol, Privacy, Efficient}`, `MPC/BGW` and `MPC`;
  - U12/U13 and their GSW downstream (11 modules);
  - root `TCSlib`.
  - `Defs` and `Shamir` were reused, because their sources equal the LE variant's.
- **Build.**
  - **25/25 rc 0.** `error:` 0, `error(` 0, substring "error" 0. `permod` found no log/record mismatch.
  - The only warnings are 15 `declaration uses 'sorry'`, in the six records-side GSW files
    (`Bootstrap` 5, `PolyRatio` 3, `Asymptotic`, `Leveled` and `LeveledSecurity` 2 each, `Circular` 1). These are
    exactly the records tip's 15 admissions in 6 files (`git grep` at `53e430b6`), rebuilt only because they
    are downstream of U12/U13.
  - The SecretSharing, MPC and CoinSampling modules have **0 `sorry` and 0 warnings**.
- **Attempt 1.** The first start failed at once (rc 1, "unknown module prefix 'Aesop'"). The scratch worktree
  had no `.lake/packages` link, so no module was elaborated; the only effect was the removal of the copy's
  `Efficiency.olean` hard link. After adding the link, the full queue ran. The record is in
  `check/build-attempt1-no-packages/`.
- **Accept.**
  - `stateplan update` took 25 modules, and `check` at `099b0f8d` gave **1470/1470 RESULT OK**, after the build
    and again at the end.
  - The 25 rebuilt oleans have link count 1.
  - The source tree `$SP/olean-replay-efh11-le` still checks 1470/1470 OK at `a299c19e` after the run and at the
    end, so nothing was written through.
- **Root and Checks.** Root `TCSlib` was rebuilt with rc 0. Neither `audits/*/Checks` is downstream of the
  change, so the state check covers both. Both were also re-elaborated as probes (`runner_full`, no `-o`):
  `garg-ch1-3` rc 0 and `pass-shelat` rc 0, each with 0 errors, 0 `sorry` and 0 warnings.
- **Admissions.** The landing diff adds 0 `sorry`, `admit`, `native_decide`, `axiom` or `opaque` tokens.
- **Axioms** (`AxiomsLand`: phase 2's `AxiomsHead` with the census extended to `Defs`, `Sharing` and
  `Protocol`). It ran with rc 0 and 0 errors; its one warning is the control's.
  - **315 stored constants in the six owners:** 180 `[Classical.choice, Quot.sound, propext]`,
    101 `[Quot.sound, propext]`, 31 `[propext]`, and 3 matchers with `[]`. None is non-standard.
  - **Against phase 2's 217 for the three new owners:** exactly one constant is gone,
    `SecretSharing.samplesEfficiently_comap`, and one is new, `recombineRaw_bgwEval_mul`. The rest are the
    frozen owners' constants, including the five new readers.
  - **Named `#print axioms`:**
    - the three `Defs` readers give `[propext, Quot.sound]`;
    - `degreeReduce_apply`, `recombine_eq_sum`, `recombineRaw_bgwEval_mul`, `dealerSamples_shamir`,
      `shamirEfficient`, `shamirEfficient_{correct, localReconstruct, perfectPrivacy}`, `reshare_dealerSamples` and
      the four `Scheme.restrict_*` transfers give `[propext, Classical.choice, Quot.sound]`.
  - The `sorry` control reports `[sorryAx]`.
- **Canonical coe-A seals.** The collector `Collect` (recipe template, 6 owners) ran with rc 0 (1,653 `CAT`
  rows). `mkseals_coe.py` (A variant, unmodified, `SEAL_CHUNK=1000`) generated the seals. Every probe has its
  install and EOF records.

  | Owner | Requests | Stored | Errors |
  |---|---|---|---|
  | `SecretSharing.Efficient` | 1,122 | 104 | **0** (F01 closed; it was 5) |
  | `SecretSharing.ShamirEfficient` | 1,145 | 99 | **0** |
  | `MPC.BGW.Efficient` | 1,186 | 14 | **0** (with `recombineRaw_bgwEval_mul`) |
  | `SecretSharing.Defs` | 0 | 45 | **0** |
  | `SecretSharing.Sharing` | 13 | 19 | 2: src `:64` `isSharing_share`, `:152` `recombine_eq_reconstruct` |
  | `MPC.BGW.Protocol` | 27 | 34 | 11: src `:99` `isSharing_degreeReduce`; `:136–139`, `:143` `bgwEval_isSharing`; `:159–160`, `:162–164` `bgwEval_of_isLinear` |

  - **The new owners' requests are 1 higher than in phase 2:** 1,121, 1,144 and 1,185 there. The new base adds
    one definition to their closure, #384's `seedModulusWord`.
  - **`Sharing` and `Protocol` keep exactly their 13 pre-existing failures (DL-68), unchanged.**
    - The request counts are the same as in phase 2.
    - The failing declarations are the same, at the base's lines shifted by +5, the 5-line reader insertions.
      The base's lines were `:64`, `:147` and `:94`, `:131–134`, `:138`, `:154–155`, `:157–159`.
    - The error messages are the same, in the same order, as phase 2's base seals (`seal-base`).
- **Paired controls** (`mkctl_efh11_land.py`, the review's `mkctl_efh11.py` with the probe directory renamed).
  `CtlS_X` is the owner's seal with the control block after the owner's closing `end`; `CtlU_X` is the owner
  source with the same block, unsealed.

  | Owner | NEG (foreign read by `rfl`/`Iff.rfl`) | POS | Sealed | Unsealed |
  |---|---|---|---|---|
  | A `Efficient` | A1 `threshold … .Auth`; A2 `encWords []`; **A3 `Scheme.Correct`, A4 `LocalReconstruct`, A5 `PerfectPrivacy`** | `threshold_auth`, `encWords_nil`, **`Scheme.correct_iff`, `localReconstruct_iff`, `perfectPrivacy_iff`** | 5 errors, one per NEG | 0 |
  | B `ShamirEfficient` | B1 `resWord`; B2 `π.encode` | `resWord_eq`, `encode_eq` | 2, one per NEG | 0 |
  | C `BGW/Efficient` | C1 `resWord`; **C3 `degreeReduce`, C4 `recombine` (sum form)** | `resWord_eq`; C2 owned `shamirResharer` by `rfl`; **`degreeReduce_apply`, `recombine_eq_sum`** | 3, one per NEG | 0 |

  **ALL_OK**, with 0 stray errors. The sealed files have no error outside the control NEG lines, so the owners
  seal at 0 with the controls in place.
- **decls2** (pinned `decls2.py`, `fa81981a`):
  - **Landing head against `5382668b`** (8 files): **146 ADDED, 0 CHANGED, 0 REMOVED.** That is the worker's 141
    minus the removed local `samplesEfficiently_comap` (140), plus 6: the three `Defs` readers,
    `degreeReduce_apply`, `recombine_eq_sum` and `recombineRaw_bgwEval_mul`.
    - The brief said to expect "the 5 new readers/theorem". The count is 5 readers plus 1 theorem.
  - **Worker commits alone** (`eebf2d35` against `5382668b`): 141 ADDED, row for row equal to the review's
    `decls2-review.tsv` with the location column dropped.
  - **Per maintainer commit:**
    - LE-h11-w1: 3 ADDED.
    - LE-h11-w2: 3 ADDED.
    - LE-h11-promote: 1 REMOVED (`SecretSharing.samplesEfficiently_comap`).
    - LE-h11-doc: empty.
- **Lint.** `campaign_style_lint --check8b` on `TCSlib/Cryptography`, run on exports of the base merged with the
  records tip (merge-tree `4d034794…`) and of the check head.
  - **FAIL:** base 92, landing 92. With line numbers normalized, the FAIL sets are identical. The pre-existing
    statement-prose FAILs in `Sharing`/`Protocol` move by +5 lines.
  - **WARN:** 103 → **101**. LE-h11-w1 and LE-h11-w2 close two check-8 WARNs: `Defs`'s
    `Correct`/`LocalReconstruct`/`PerfectPrivacy`, and `Protocol`'s `degreeReduce`.
  - **No new FAIL or WARN line.** The INFO delta is the three new files and the line counts, including
    "`ShamirEfficient.lean` 984 lines > target 600".
  - **`style_lint.py`:** the three new files have 0 findings. `Defs`/`Sharing`/`Protocol` have 10 findings, the
    same as at the base (missing docstrings on pre-existing theorems). The two facades' missing `set_option`
    lines are the same as at the base.
- **Lean slots.** There were three queues: the build, the probes and the seals with the controls. Every start
  checked `pgrep -fc "bin/lean "` ≤ 2 and free disk ≥ 2,048 MB (`check/slot.log`).
  - The host had at most 2 other Lean processes. There was no wait, and none was killed.
  - Free disk stayed at about 5.9–6.1 GB.

## Notes

- **The three LE-h11-w1 readers keep the worker's one-line docstrings** ("The defining equation of
  `Correct`.", and so on), because EF-H11-R1 grants the W1 patch verbatim.
  - By the standard of R4 and policy §2 these are bare labels. The `iff` statements give the formula.
  - A follow-up docstring pass, or a later `Defs` owner change, could align them with the W2 readers' "Glue."
    form. This is not done here, as it is outside the rulings.
- **DL-63** (EF-R23-R2): nothing is decided here about re-pointing EF-H11's scalar leaves `addModW`/`mulModW`
  to EF-R2/R3's `ModularArithmetic.addMod`. They land as delivered, and the ledger row stays open.
- **Follow-ups, not in this PR:**
  - EF-H11-R3 (A): the interface-strengthening statement item (`enc*_injective`, `adm_eventually`; the Shamir
    instance at an unbounded coin bound).
  - EF-H11-R6 (A): the circuit encoding and the tree-evaluation host, then the whole-circuit evaluator in wave 2.
- **DL-67** (one public `Fin p ≃ ZMod p`) and **DL-68** (the 13 `Sharing`/`Protocol` seal failures) remain as
  recorded. `recombine_eq_sum` now exists for the later repair of `isSharing_degreeReduce`.

## State after the job

- **Kept for the Codex gate.** The replay holds 5.9 MB of unique data beyond its hard links. The rest of
  `$SP/land-efh11/` is about 270 MB: three sparse worktrees of about 60 MB each, the 40 MB evidence extraction
  and the 24 MB lint exports.
  - `$SP/land-efh11/replay`: the olean tree accepted at check head `099b0f8d`. Its state is
    `$SP/land-efh11/check/state.json`.
  - `$SP/land-efh11/mergewt`: the scratch worktree at `099b0f8d`, with probes under `EFH11Land/`.
  - `$SP/land-efh11/wt`: the landing worktree on `land/ef-h11-sharing-bgw`.
  - `$SP/land-efh11/dwt`: the decls2 checkout.
  - Delete all four after the gate, with `git worktree remove` for the three worktrees.
- **Superseded:** phase 2's `$SP/olean-replay-efh11` and `$SP/olean-replay-efh11-le` (this job only read and
  hard-linked the latter). Their owner may delete them.
- **Records:** `$SP/land-efh11/check/` holds `plan/`, `build/`, `permod.*`, `stateplan-*`, `statecheck-*`,
  `snapverify-*`, `slot.log`, `rule10/` (probe and seal runs, `seals-coe-A.tsv`, `controls.txt`), `decls2/`,
  `ax-land.txt` and `ax-p2.txt`. `$SP/land-efh11/lint/` holds the lint outputs, and
  `$SP/land-efh11/{ledoc.py,doconly.py,ctleval.py,rule10.sh,runq.sh}` are the drivers.

## Draft PR body

Use base `iO/phase-a-base` and head `land/ef-h11-sharing-bgw`, and open it as a **draft**.

Title: `EF-H11: efficient secret-sharing interface, Shamir instance, BGW resharer and gate steps`

```markdown
Efficiency wave 1, job EF-H11 (`ef-h11-sharing-bgw`). It states the efficiency clause of [PS10, Def 152.1] for
secret sharing, which `SecretSharing.Scheme` does not model, and proves it for Shamir's scheme over `ℤ_p`. It
also shows that every step a BGW party performs over `ℤ_p` is a polynomial-time word map, uniform in `p`.

**Stacked PR.** The base is `iO/phase-a-base` (`5382668b`), which merges #374, #378, #384 and #380, all still
open. This PR lands after those four, like #387 and #393. Its own diff is 10 commits and 8 files, +1,811/−0.

## Contents
- `SecretSharing/Efficient.lean` (new) is the interface:
  - `Scheme.restrict`, with correctness, locality and privacy transfer;
  - `DealerSamples`: the dealer's coins in the `CoinSampling.SamplesEfficiently` form, with the parameter word
    computed in polynomial time;
  - `EfficientScheme`: uniform `PolyTimeComputable` share and listed reconstruction;
  - `EfficientScheme.Correct`/`LocalReconstruct`/`PerfectPrivacy`, defined through the existing `Scheme` notions
    at every public parameter;
  - the residue layer `resWord`, `addModW`, `subModW`, `mulModW`, `invModW` (Fermat), with exactness and
    polynomial time.
- `SecretSharing/ShamirEfficient.lean` (new) is the Shamir instance `shamirEfficient b`:
  - the share machine `shareRaw` and the recombination machine `recombineRaw` (counted loops on
    `BinArith.forLoop`), with their specs and `PolyTimeComputable` proofs;
  - the dealer's coins: `dealerSamples_shamir`, via the bucket sampler and `CoinSampling.samplesEfficiently_comap`;
  - correctness, locality and privacy, **transferred** from `Shamir.correct`, `localReconstruct` and
    `perfectPrivacy`, not re-proved.
- `MPC/BGW/Efficient.lean` (new) covers BGW over `ℤ_p`:
  - Shamir re-sharing with explicit coins (`shamirResharer`, `polyTimeComputable_reshare`,
    `reshare_dealerSamples`);
  - the input, constant, addition and scalar gates;
  - the multiplication gate's local product and recombination, closed against `bgwEval_mul` by
    `recombineRaw_bgwEval_mul`.
- The `SecretSharing` and `MPC/BGW` facades get imports and Contents lines.
- Readers beside the frozen definitions (landing edits):
  - `Scheme.correct_iff`, `localReconstruct_iff` and `perfectPrivacy_iff` (`SecretSharing/Defs.lean`);
  - `Shamir.recombine_eq_sum` (`SecretSharing/Sharing.lean`);
  - `MPC.BGW.degreeReduce_apply` (`MPC/BGW/Protocol.lean`).

## Commits
1–6. `71acf81c`, `053f16ff`, `f7190304`, `a71f6ef3`, `ae444a22`, `eebf2d35`: the worker's six commits, applied
   with `git am`. Authorship and messages are kept, and the files are byte-identical to the delivery.
7. `a5a4ef90` **LE-h11-w1** (EFH11-F01; EF-H11-R1 by EF-W1-R (A)). The three `Iff.rfl` readers in `Defs.lean`,
   and the four transfer proofs now read through them (the worker's patch, verbatim).
8. `e92e9437` **LE-h11-w2** (EFH11-F02; EF-H11-R2 (A)). `degreeReduce_apply` and `recombine_eq_sum` (`rfl`),
   and `recombineRaw_bgwEval_mul` with a real docstring.
9. `89380ebe` **LE-h11-promote** (EFH11-F05; EF-H11-R5 (A), DL-66). The local `samplesEfficiently_comap` is
   deleted in favour of #384's `CoinSampling.samplesEfficiently_comap` (proof-only re-point).
10. `11ea959f` **LE-h11-doc** (EFH11-F04; EF-H11-R4 (A)). Docstrings only: "Glue." notes on 86 declarations, and
    formulas for 10 bare readers.

All ten commits are signed.

## Checks
- **Maintainer review:** ACCEPT WITH LANDING EDITS (`briefs/efficiency-gaps/wave1/EF-H11/final-r1/`). All its
  landing edits are applied; landing record `landing.md`.
- **Merged-tree replay of the landing head** with the records tip `53e430b6` (Lean = `bff0567b` + U12/U13), on a
  copy of phase 2's state-checked tree:
  - 25 modules rebuilt with rc 0 and 0 errors, including root `TCSlib`. The 15 `sorry` warnings are the records
    side's GSW admissions; the SecretSharing/MPC/CoinSampling modules have 0 `sorry` and 0 warnings.
  - The state check gave 1470/1470 OK.
  - Both `audits/*/Checks` re-elaborate with rc 0.
- **Axioms:** all 315 constants stored by the three new owners and `Defs`/`Sharing`/`Protocol` are within
  `{propext, Classical.choice, Quot.sound}`. The targets and the new readers are standard.
- **Canonical coe-A seals:**
  - **0 errors** for `SecretSharing/Efficient` (F01 closed), `SecretSharing/ShamirEfficient`, `MPC/BGW/Efficient`
    and `SecretSharing/Defs`.
  - `Sharing`/`Protocol` keep exactly their 13 pre-existing failures (ledger DL-68), unchanged.
  - The paired controls, including the five new readers, are ALL_OK.
- **decls2** against the base: 146 added, 0 changed, 0 removed. That is the delivery's 141, minus the promoted
  local `samplesEfficiently_comap`, plus the 5 readers and `recombineRaw_bgwEval_mul`.
- **Lint:** no new FAIL or WARN. Two check-8 WARNs are closed by the readers. `style_lint` reports 0 findings
  on the new files.

## Still to do
- **A Codex gate is to be staged** for this PR.
- Merge after #374, #378, #384 and #380.
- **Follow-ups, not in this PR:**
  - EF-H11-R3: the interface-strengthening statement item, with encoding injectivity and `adm_eventually`.
  - EF-H11-R6: the circuit encoding and the tree-evaluation host for the whole-circuit evaluator, then the
    evaluator in wave 2.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA
```
