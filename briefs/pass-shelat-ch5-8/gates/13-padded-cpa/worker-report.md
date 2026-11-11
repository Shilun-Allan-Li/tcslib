# Fill report · `padded-cpa` · final

**Worker** Claude (external fill, exchange push route). **Issue base**
`4a09f3993eb9344fc5714610e41ab141a0144db8` on `cryptography/pass-shelat-ch2-4`. **Proof branch**
local `fill/padded-cpa` at `24747c9d8` (4 commits over the base; never pushed). **Pack** read at exchange
`cc07d65f9`; `sha256sum -c SHA256SUMS` in `outbox/fills/padded-cpa/`: all 7 OK. Source hashes:
`sha256sum -c SOURCE-SHA256SUMS` from a clean base worktree, 221/221 OK
(`evidence/logs/source-sha256.log`).

## 1. Result

**`BitPublicKeyScheme.SingleBitSecure.padded_cpa` is proved.** No admission remains in the
touched files. The frozen statement is unchanged (diff of the declaration: body only). Axioms:
`[propext, Classical.choice, Quot.sound]`.

The proof follows the brief's route and proves the exact identity, not only a bound: for the
machine `D` of T1, at every `n`,
`advantage (S'.indGame .cpa A q false n) (S'.indGame .cpa A q true n) =
distAdv (S.pkEncDist n false) (S.pkEncDist n true) (D.distinguisherL n)`
(`padded_cpa_advantage_eq`); then `singleBitSecure_iff` and `INDSecure_iff` close the goal with
`ε` the right side.

| Brief step | Delivered as |
|---|---|
| 1 eager challenge coins | `expect_simulate_indImpl_cpa` (private, `OracleSecurity.lean`): for every `G`, `𝔼[G ∘ fst]` of the lazy simulation from any state equals `𝔼_re` of `G` of the deterministic run `ChallengeSim.chRun` with challenge answer `Enc(m_b; re)`. Induction on the computation; the unused coins marginalize out by `chRun_some_congr` and `expect_const`. |
| 2 first-challenge congruence | `ChallengeSim.chRun_congr`: `chRun g c none = chRun g' c none` whenever `g, g'` agree at the first challenge query `firstQ c` (vacuous without one); `firstQ` does not mention `g`. Induction. |
| 3 distinguisher `D` (T1) | `Games.exists_handlerMachine` with `k = 2`, `din = recDin L = [L, 2]`, `dout = recDout L = [2, L]`, `dα = .const 1`, and `H = ChallengeSim.recHandler L (cpaAns L) _`: `seedLen = 0`, state `[asked, m₀, m₁]` (initially `000`), `advIn ⟨1^n, ⟨z, ω⟩⟩ = pairFstD z`, `Dec` answered `00`, every challenge answered `padCt L(n) (pairSndD z)` with the first query recorded, `out` = `[a]` for `(0,1)`, `[¬a]` for `(1,0)`, `[0]` otherwise. All four functions are built from the closure combinators (`polyTimeComputable_recRun`, `polyTimeComputable_recOut`, `polyTimeComputable_cpaAns` as `polyTimeComputable_padEncFun`). Its simulation is `chRun` with the constant answer, with final state `firstQ` (`simulate_recHandler_init`). |
| codec alignment | `din/dout` evaluate to `S'.inLens n`/`S'.outLens n` only propositionally (`hins`, `houts`, by the published `inLens_*`, `outLens_*`, `padded_*`, `PolyExpr.eval_const`). The transport is done once, generically, by `subst` (`ChallengeSim.chRun_toCompOn_transport`, also over `dα.eval n = 1`). |
| 4 identity | `padded_cpa_advantage_eq`: game side by step 1, step 2 and the coin transport `NUPPT.coinsCongr (padEnc_coins …)`; `D` side by `Bridge.acceptProb_eq`, T1's `φ` (`expect_sample_equiv`), the empty seed (`expect_sample_unique`), and `NUPPT.distinguisherL_eq`; the pointwise case split on `(m₀, m₁)` is `ChallengeSim.expect_indicator_sub`. |

**Edge cases.** The computation is treated abstractly, so the proof is uniform in the budget
(`q = 0` included) and in the codec's timeout output `zeroBits 1`, which is just `A`'s output
value on both sides. A run with no challenge query is the `firstQ = none` branch (both games
equal, `D` outputs `[0]`: `recOut_init`). Repeated challenge queries return the recorded
ciphertext in the game (`indImpl_challenge_repeat`, `chRun_query_one_some`) and the same
`padCt L(n) c` in `H` (`recRun_recorded`, `simulate_recHandler_recorded`).

**Checkpoints.** Steps 1–4 were completed together; checkpoint 1 (exchange `482bfaa57`) already
carried the complete proof (proof-branch `747b9c2a7`). Commit 4 then removed the definitional
readings that the seal found (§5) without changing the route.

## 2. Changed files and declarations

`git diff --stat 4a09f399..24747c9d8`: 3 files, 889 insertions, 12 deletions.

| File | Lines | Change |
|---|---|---|
| `TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean` (owned) | 705 → 976 | 3 imports added; new private section before the target; target body; target sketch; one status phrase in the module docstring |
| `…/PublicKey/OracleSecurity/ChallengeSim.lean` (new helper) | 273 | generic: deterministic CPA run, first query, congruence, transport, sampling identities |
| `…/PublicKey/OracleSecurity/RecordHandler.lean` (new helper) | 333 | generic in `Lc` and `ans`: the recording `PolyHandler` and its simulation |

Both helpers import neither `OracleSecurity` nor anything downstream of it; `OracleSecurity`
imports both explicitly. All files are below 1000 lines. Statements, other declarations, the
statement prose and global simp attributes are unchanged. **Sketch edits:** the target's
`**Proof sketch.**` was rewritten to describe the delivered proof (eager coins, congruence, the
recording handler, the exact identity); the module docstring's "Main results" line lost
"(stated; a `sorry` under its sketch)".

**New imports of `OracleSecurity`:** `Games.Bridges.Experiments` (`Bridge.acceptProb_eq`,
`acceptGame_eq`), `…OracleSecurity.ChallengeSim`, `…OracleSecurity.RecordHandler` (which imports
`Games.Efficiency` for T1 and `Complexity.ClassNP.PolyTimeBlockLoop` for `headD`, `tail`, `not`).

**New public declarations** (each with a docstring stating its formula, and a sketch when
nontrivial; definitions with case or `_eq` lemmas, the structure with `simps` field equations):
- `ChallengeSim` (namespace `TCSlib.Cryptography.Composability.ChallengeSim`): `chRun` (+
  `chRun_pure`, `chRun_query_zero`, `chRun_query_one_none`, `chRun_query_one_some`), `firstQ` (+
  `firstQ_pure`, `firstQ_query_zero`, `firstQ_query_one`), `chRun_some_congr`, `chRun_congr`,
  `length_of_firstQ_eq_some`, `chRun_toCompOn_transport`, `expect_sample_equiv`,
  `expect_sample_prod`, `expect_sample_comm`, `expect_sample_unique`, `expect_sub`,
  `expect_indicator_sub`.
- `RecordHandler` (same namespace): `recDin` (+ `_zero`, `_one`), `recDout` (+ `_zero`, `_one`),
  `recRun` (+ `recRun_eq`, `recRun_dec`, `recRun_fresh`, `recRun_recorded`,
  `polyTimeComputable_recRun`), `recOut` (+ `recOut_eq`, `recOut_init`, `recOut_recorded`,
  `polyTimeComputable_recOut`), `recAdvIn` (+ `recAdvIn_eq`), `recHandler` (+ `simps` equations
  `recHandler_stateLen/_seedLen/_init/_run/_advIn/_out`, `isSimp := false`),
  `simulate_recHandler_recorded`, `simulate_recHandler_init`.
- They are public because `OracleSecurity` uses them (helper modules).

**New private declarations in `OracleSecurity.lean`:** `cpaAns` (the challenge answer
`padCt L(n) c` read from the context), `polyTimeComputable_cpaAns`, `cpaAns_seedIn`,
`ofFn_splitHalf_bit`, `expect_simulate_indImpl_cpa` (step 1), `padded_cpa_advantage_eq` (step 4).

**Duplication: none.** A search of `TCSlib` found no existing lemma of the forms of the sampling
identities; the closest is `Bridge.expect_sample_pair` (sequential sampling equals product
sampling), a different statement. **Reader requests: none blocking.** One remark for the shared
layer: the exact-length padding lemma used here is `GGMRed.ofFn_padFin_of_length` (in
`Pseudorandom/Functions/Asymptotic/GGM/Run.lean`); a copy exists in `Asymptotic/HardCoreGLColl`.
Its natural home is beside `padFin` in `Asymptotic/Adversary.lean` (pre-existing duplication, not
introduced here).

## 3. Environment, cache and bootstrap

Preflight (`logs/preflight.log`, before any cache or Lean work):
- `nproc` 4. cgroup v1 (`…/claude-code-bash`): `memory.limit_in_bytes` 14,337,298,432;
  in use = `usage − total_cache + total_shmem` = 4,237,475,840 − 4,073,332,736 + 0 = 164,143,104;
  **headroom 13,516 MiB** (floor 4 GiB). `oom_kill 0`, `failcnt 0` at preflight and at the end;
  peak `max_usage_in_bytes` 12,736,491,520 (includes page cache).
- Clone `/home/user/fill` and scratch `/tmp/claude-0`: `/dev/vda`, ext4 (no tmpfs).
  **26,194,386,944 B free** (floor 12 GiB); re-check before the cache 23,608,496,128 B (floor 8 GiB);
  19,134,824,448 B free at the end.

Toolchain: elan installed after the preflight, `leanprover/lean4:v4.25.0` (Lean 4.25.0,
`cdd38ac5…`) (`logs/toolchain.log`). The proof checkout is a separate worktree of the base
(`/home/user/fill`, local branch `fill/padded-cpa`); `.lake` lives only there.

Cache (`logs/cache-store.log`, `cache-get.log`, `mathlib-roots.txt`, `packages.log`,
`cache-probe.log`):
- Archive store `~/.cache/mathlib` **absent** before the fetch (0 files, 0 bytes); every archive
  was downloaded by this session.
- Narrowed fetch for the **97 roots** (identical to the pack's `roots.txt`) with
  `TAR_OPTIONS=--no-same-owner`: "Attempting to download 2370", "Decompressing 2370", 0 failed,
  exit 0. No zero-size olean. The unfiltered `lake exe cache get` was never run; no `lake build`.
- Packages: the 11 present packages match the manifest's URL and revision; `doc-gen4`,
  `UnicodeBasic`, `BibtexQuery`, `MD4Lean` are ABSENT and imported by no module of the order. Last
  line: `package check: PASS (0 mismatches)`.
- Probe: a file importing the first root elaborated through `scripts/lean_check_tree.sh` (exit 0).

Bootstrap (addendum item 5, owned file's upstream first):
- `logs/bootstrap.log`: the 101 modules of the issued order that `PublicKey/OracleSecurity`
  imported at the base (`logs/bootstrap-upstream.txt`), all exit 0.
- After the new imports (§6): the 46 further modules of the new upstream closure
  (`logs/bootstrap-upstream2.txt`), all exit 0 (`logs/bootstrap2.log`). An earlier attempt to build
  the 10 added T1 modules alone failed only on missing oleans of not-yet-built prerequisites
  (`logs/bootstrap-added.log`, item 8: not findings).
- The rest of the order was built by the final sweep.

Resources: one Lean process at a time throughout (every check through `chk.sh` →
`scripts/lean_check_tree.sh`, sequential; no self-imposed timeouts; start, end, elapsed and the
peak RSS of each check are logged). Peak Lean RSS 3,065 MiB (sweep); longest module 68 s
(`Asymptotic/OneWayYao`). No shortage, no exit 135/137/139, no ENOSPC.

**One interrupted sweep.** The first final sweep was stopped by me after 15 modules to fix the
readings described in §5 (`logs/sweep-aborted-1.log`); the module being checked
(`Build/Primitives`, whose olean the script had removed) was rebuilt before continuing
(`logs/dev-checks.log`). The authoritative sweep is `logs/sweep.log`.

## 4. Checks

Module checks during development: `logs/dev-checks.log` (`ChallengeSim`, `RecordHandler`,
`PublicKey/OracleSecurity`, each one call of `scripts/lean_check_tree.sh`).

**Final sweep** (`logs/sweep.log`, proof-branch `24747c9d8`): all **233 modules of
`order-final.txt` passed, 0 failed**, including `PublicKey/OracleSecurity` and
`PublicKey/TrapdoorCPA` (positions 159–160, rechecked after the two helpers) and every module
downstream of the owned file. The three touched modules have **no error and no warning**.

**Admissions** (`logs/sorry-census.txt`, positions of the `declaration uses 'sorry'` warnings
read back to declaration names): **30**, i.e. `base-sorries.txt` (31) minus exactly
`BitPublicKeyScheme.SingleBitSecure.padded_cpa`; nothing added.

**Axioms** (`logs/axioms.log`, `seal/Axioms.lean`):
- `BitPublicKeyScheme.SingleBitSecure.padded_cpa`: `[propext, Classical.choice, Quot.sound]`.
- `TrapdoorCollection.tdpBitScheme_padded_cpa`: `[propext, Classical.choice, Quot.sound]` (it
  inherits no admission).

**Lint** `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Encryption/PublicKey
--check8b`: before (clean base worktree) 0 FAIL, 6 WARN over 15 files; after 0 FAIL, the same 6
WARN (all in untouched files) over 17 files (`logs/lint-before.log`, `logs/lint-after.log`). The
two helpers and the owned file have no WARN (check 8 and 8b included). No new line exceeds 100
characters.

## 5. Readings: scan, seal, controls, explicit unfolds

- **Scan** (`seal/SealScan.lean`, `logs/seal-scan.log`; adapted from the s2b-efficiency scan).
  Roots: every declaration of the two helpers, the target and the six private helpers of
  `OracleSecurity`: 63 roots, 68 declarations scanned with their auxiliary declarations
  (matchers, `proof_`, `eq_`, internal names).
  - **59 foreign TCSlib definitions; 41 regular (sealable)**, listed in `seal/candidates.txt`:
    `NUPPT.{coinLen, coinsCongr, distinguisherL, runAt, toCompOn}`, `PolyExpr.eval`,
    `PolyTimeComputable`, `pairFstD`, `pairSndD`, `pairEncode`, `pairDecode`,
    `BitPublicKeyScheme.{SingleBitSecure, pkEncDist}`, `FixedLengthScheme.splitHalf`,
    `Bridge.acceptGame`, `OracleComp.bind`, `PolyHandler.{advInput, answer, impl, input, result}`,
    `ProbComp.{expect, prob, sample}`, `accept`, `advantage`, `acceptProb`, `distAdv`,
    `Negligible`, `bitCodec`, `seedIn`, `simulate`, `zeroBits`, `padFin`, and the helper
    definitions `chRun`, `firstQ`, `recDin`, `recDout`, `recOut`, `recAdvIn`, `recHandler`
    wherever another module uses them.
  - **Instances:** the scan records every TCSlib instance in the roots' terms: **none**.
  - **Not sealable (18):** reducible abbreviations, projections and auxiliary recursors, read as
    notation: `NUPPT.Coins`, `ProbComp`, `bitSpec`, `bitSpecAt`, `unifSpec`,
    `OracleSpec.dom/rng`, `BitPublicKeyScheme.gen/enc`,
    `PolyHandler.{advIn, init, out, run, seedLen, stateLen}`, `OracleComp.{casesOn, brecOn, below}`.
- **Sealed copies** (`seal/Seal{ChallengeSim,RecordHandler,OracleSecurity}.lean`, generator
  `tools/mkseal.py`, `logs/mkseal.log`): verbatim copies with every regular foreign definition the
  file's touched declarations use made `local irreducible` (6, 16 and 38 names), each importing
  only the original's imports; for `OracleSecurity` the seal starts at the touched section. **All
  three elaborate with exit 0 and no warning** (`logs/seal.log`).
- **What the seal caught** (fixed in proof-branch commit 4, `logs/seal-dev.log`): three steps of
  `RecordHandler` read `seedIn` (twice) and `PolyExpr.eval` (a length through `List.ofFn` of a
  two-bit vector) by definitional unfolding; a review for the same pattern removed `rfl`/`exact`
  steps through `PolyExpr.eval (.const _)`, `simulate` (pure case) and `chRun` (from
  `OracleSecurity`). All now go through `seedIn_eq`, `PolyExpr.eval_const`, `simulate_pure` and the
  `chRun_*` equations.
- **Controls** (`seal/SealControls{Unsealed,Sealed}.lean`): seven readings through a body
  (`PolyExpr.eval`, `zeroBits`, `padFin`, `seedIn`, `simulate`, `chRun`, `recDin`). **All seven pass
  unsealed and fail sealed** with the full 41-name candidate list (lines 11, 13, 15, 18, 21, 24, 26
  of `SealControlsSealed.lean`), so the seal is active.
- **Explicit-unfold scan** (`tools/rwids.py`, `seal/RwIds*.lean`, `logs/rwids.log`,
  `logs/rwids-files.tsv`). `irreducible` does not block `rw [f]`, `simp [f]` or `unfold f`, so every
  identifier the added lines pass to `rw`, `rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`,
  `dsimp` or `unfold` was resolved in its file's namespace and `open`s: 169 in total
  (38 + 40 + 91).
  - 137 resolve to theorems. The rest are local hypotheses (`h`, `ih`, `hans`, …), the
    dot-notation `S.indImpl_dec_cpa/_challenge_none/_challenge_repeat` (the owned file's own
    theorems), the owned file's private lemmas `cpaAns_seedIn` and `ofFn_splitHalf_bit`, and `rfl`
    (the proof term of a `show (true != false) = true from rfl` rewrite).
  - **The only definition passed is `cpaAns`**, the owned file's own private definition, in
    `polyTimeComputable_cpaAns` and `cpaAns_seedIn`. `padCt` is read through `padCt_eq`. No core,
    Mathlib or foreign TCSlib definition is passed.
- Other conversions: the owned file's own definitions `padded`/`ofPadded`, `indCodec`, `inLens`,
  `outLens` are crossed definitionally in a few `exact`/`:= hq` steps (allowed by the brief for
  `OracleSecurity.lean`'s own definitions; they stay unsealed in the sealed copy).

**Readings disclosed: none of a foreign definition.**

## 6. Order and roots

`OracleSecurity` now imports `Games.Bridges.Experiments` and (through `RecordHandler`)
`Games.Efficiency`, as the brief's interface table requires. Their closure adds **10 modules** that
were not in the issued `order.txt` (`Games/Bridges/{QueryTree, Machines, Experiments}`,
`Games/Efficiency/{Strings, Replay, Handler, OracleBridge, Interactive, InteractiveSpec}`,
`Games/Efficiency`); with the two new helpers, **12 modules** are inserted immediately before
`PublicKey/OracleSecurity`, giving `logs/order-final.txt` (233 modules; `diff` with the issued order
shows exactly these 12 insertions; `tools/topo.py`: every import precedes its importer). None of
the 12 imports anything downstream of `OracleSecurity`. **Roots unchanged**: the 97 Mathlib roots
of the final order equal the pack's `roots.txt` (`logs/mathlib-roots-final.txt`), so no further
cache fetch was needed.

## 7. Payload

**Delivery commits.** The commit `fill padded-cpa: final` (`06bc7b21d`) and checkpoint 1 omitted
`evidence/`: a local Git exclude entry (`evidence/`, added for the proof worktree, which shares
the object store with the exchange checkout) hid it. The exclude entry was removed and the
following commit, also titled `fill padded-cpa: final`, adds `evidence/` and this note; the
delivery is the path at that commit. Nothing else changed: `REPORT.md` differs only by this
paragraph, and `patches/` and `src/` are identical.

`REPORT.md`; `patches/` = `git format-patch 4a09f399..24747c9d8` (4 patches); `src/` = the three
owned paths at `24747c9d8`; `evidence/{logs,seal,tools}`. `PAYLOAD-SHA256SUMS` covers every file. Applying the 4 patches with `git am` to a clean base
worktree reproduces `src/` byte for byte and the proof branch's tree (`logs/patch-reproduce.log`).
Commits on the proof branch:
1. `e952cb383` deterministic CPA challenge run and sampling identities (`ChallengeSim`);
2. `ddcdcd8cf` the recording handler (`RecordHandler`);
3. `747b9c2a7` the proof of `padded_cpa` (checkpoint 1);
4. `24747c9d8` read foreign definitions only through their published lemmas (seal findings),
   `padCt_eq`, line wraps.

**Final payload delivered — ready for maintainer review**
