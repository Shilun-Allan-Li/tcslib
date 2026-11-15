# Fill learning — checkpoint 2 (steps 1 and 2)

**Unit** `learning` · **Worker** Claude · **Issue base** `107f1e8c218733eac12d6b9bee6fece441271317`
(`cryptography/pass-shelat-ch2-4`) · **Proof branch** `fill/learning` (local), checkpoint commits
`c323e6041a6696356bca538366c219dc04f464a1` (1) and `d80d3e5e3528cdf3086662f185ef331eba5a9fff` (2) ·
**Lean** 4.25.0, Mathlib at the base's manifest.

**Target status at this checkpoint:** `Randomness.predictAdv_prfConcept_negligible` is still
`sorry`. Steps 1 and 2 of the route are proved (no `sorry`).

## 0. Checkpoint 2: step 2, as proved

New helper `Randomness/Learning/Random.lean` (203 lines), imported by the owned file:
`abs_gameProb_random_sub_half_le`: for `n ≥ 1`, every learner `ℓ` and `m` examples,
`|gameProb m (fun R => R) ℓ − ½| ≤ m / 2^n`, the game with a uniform random function
`R : {0,1}^n → {0,1}^n` in place of the keyed family (with step 1, `acceptProb (randomFunction …) D`
is this game, `randomFunction_apply`).

- Put `R` last and average over it first (`uprob_comp_equiv`, `uprob_prod`). For fixed examples
  `s`, coins `r` and fresh point `x`:
  - if `x` is none of the examples, `flipAt hn x R = update R x (flip0 (R x))` (flip the first bit
    of `R x`) is an involution of the functions (`flipAt_involutive`) that keeps the labels of the
    examples (`Function.update_of_ne`) and negates the label of `x` (`firstBit_flip0`); it maps the
    winning functions onto the losing ones, so the probability is exactly `½` (`uprob_flip_half`,
    `uprob_comp_equiv`, `uprob_not`);
  - otherwise the probability is in `[0, 1]`.
- So `|gameProb − ½| ≤ Pr[∃ j, s_j = x]` (the average of `|p − ½| ≤ [x ∈ s]`), and the union bound
  (`uprob_exists_le`) with `Pr[s_j = x] = 2^{-n}` (`uprob_prod`, `uprob_eq_point`) gives `m / 2^n`.
- `n ≥ 1` is needed for the first bit; at `n = 0` the final step uses an eventual bound.

New declarations: `flip0` (`flip0_eq`, `flip0_flip0`), `firstBit_of_pos`, `firstBit_flip0`,
`flipAt` (`flipAt_eq`, `flipAt_involutive`), `uprob_flip_half`, `uprob_eq_point`,
`abs_gameProb_random_sub_half_le`.

Overlap (step 2): the flip argument has no TCSlib relative (searched `update`/`involutive`/`flip`
with `uprob` in `TCSlib/Cryptography`); `uprob_eq_point` (`Pr[x = y] = 1/2^n`) is the uniform
point mass, which `Rejection.uniform_probTrue` would give through `FinDist`; the `uprob` form is
stated directly from `uprob_eq_card_filter`. The PRFGame collision bound
(`OracleFromPRF/Collision.lean:375`, `abs_expect_fImpl_sub_le`) bounds the repetition of a nonce
in the CPA game (lazy sampling, `q²/2ⁿ`); here the bad event is one fixed point among `m` samples,
bounded directly.

Evidence added: `logs/checkpoint2-checks.log` (status 0; the one `sorry` warning is the target),
`checkpoint2-axioms.log` (`propext`, `Classical.choice`, `Quot.sound`), `checkpoint2-lint.log`
(92 FAIL / 101 WARN, the base's line sets), `checkpoint2-width.log`, `checkpoint2-repro.log`
(both hashes reproduced), `probes/AxiomsCP2.lean`.

## 1. Environment (addendum v1)

- **Preflight** (`evidence/logs/preflight.log`): 4 CPUs; cgroup v1 limit unlimited, so the headroom
  is `MemAvailable` = 16489095168 B = 15.36 GiB; the clone's filesystem (ext4, `/dev/vda`) has
  18171547648 B = 16.92 GiB free (floor 12 GiB): `PREFLIGHT PASS`. Before the preflight the disk had
  9.87 GiB free (below the floor); with the user's approval in the session, the two git worktrees
  of this host's finished, delivered fills (`/workspace/dlc`, `/workspace/ett`) were removed
  (`git worktree remove`; their branches are kept). No dependency tree was copied or moved.
- **Clone:** a new worktree `/workspace/learn` of the local repository, branch `fill/learning` at
  the issue base. Its source files match `SOURCE-SHA256SUMS` (246 files, `source-sha256.log`).
- **Cache:** the store (`~/.cache/mathlib`, `cache-store.log`) already held 2402 archives, left by
  this host's earlier fills. The narrowed `lake exe cache get` for the 82 roots
  (`mathlib-roots.txt`, the same list as the pack's `roots.txt`) cloned the packages of the
  manifest, printed "No files to download" and "Decompressing 2125 file(s)", and exited 0
  (`cache-get.log`). No zero-size olean. The probe importing `Mathlib.Algebra.BigOperators.Field`
  elaborates (`cache-probe.log`, `probes/CacheProbe.lean`).
- **Packages** (`packages-check.log`): `RESULT: all present packages match the manifest`
  (`doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean` ABSENT; no module of the order imports them).
- **Bootstrap** (`bootstrap.log`): the 246 modules of `order.txt`, one `scripts/lean_check_tree.sh`
  call each (through `tools/check.sh`, with start/end time and max RSS), in order: 246/246 status 0,
  no error. No host restart. Sorry census = `base-sorries.txt` (20 declarations in 10 modules;
  `census-bootstrap.txt`, `census-bootstrap-vs-base.diff`: identical).

## 2. Step 1, as proved

New helper modules (namespace `TCSlib.Cryptography.Randomness.LearnPRF`):

| File | Lines | Role |
|---|---|---|
| `Randomness/Learning/Sample.lean` | 259 | the learner's input and the last label, as polynomial-time functions of the encoded tuple |
| `Randomness/Learning/Distinguisher.lean` | 136 | the distinguisher `exists_learnDist` |
| `Randomness/Learning/Law.lean` | 173 | the game probability; prediction game and acceptance probability |

The owned file imports the three modules (and nothing else changes in it at this checkpoint).

- **The distinguisher** (`exists_learnDist`): for a learner machine `A` and a polynomial `m`, a
  next-query machine `B` whose coins at `n` are, by a bijection `φ`, `m(n) + 1` points `ρ` and
  `A`'s coins `c`, and whose tree with budget `m(n) + 1` against any oracle `g` evaluates to
  `decide (A(⟨S, ⟦ρ_m⟧⟩; c) = [true]) == firstBit (g ρ_m)`, with `S` the nested labelled examples
  `⟨⟦ρ_j⟧, [firstBit (g ρ_j)]⟩` of the first `m(n)` points. It is the public query chain
  `MultiMsg.exists_queryChain_nuppt` (non-adaptive queries at points from the coins, here with the
  zero message vector) of the machine `C` that runs `A` on `learnIn m` (`NUPPT.exists_compParam`)
  and compares with `lastLabel m` (`NUPPT.exists_seq` with the uniform machine of `verdictFun`).
  So no T1/T2/T4 run is needed: the query chain already gives a next-query machine
  (`toOracleAdversary`) at `ℓ₁ = ℓ₂ = n`.
- **The learner's input** (`learnIn_tupleWord`, `lastLabel_tupleWord`): the encoded tuple is the
  concatenation of `m(n) + 1` blocks of `6n + 6` bits; a fold of pairs ending in `[]` is a
  concatenation (`foldr_pairEncode_nil`), so the labelled sample is the block map of `relabel` over
  the first `m(n)` blocks (`MultiMsg.flatMap_range_blocks`), polynomial-time by
  `Complexity.polyTimeComputable_blockMap`, `polyTimeComputable_pairTakePoly`/`DropPoly`.
- **The law** (`exists_learnDist_acceptProb`, `predictSuccess_eq_uprob`): for every keyed family
  `G : K → {0,1}^n → {0,1}^n`, `acceptProb G (oracleDist (B.toOracleAdversary n n n (m(n)+1)))` is
  `gameProb (m n) G (learnerFn A n (m n))`, the uniform probability over `((k, (s, r)), x)` of
  `learnerFn … (label (firstBit ∘ G k) s) r x == firstBit (G k x)`; the coins are relabelled by
  `φ` and `snocEquiv` (examples, then the fresh point). The prediction game is the same uniform
  probability: its law is a product of uniform laws (`iid_uniform`, `Rejection.uniform_prod`,
  `Rejection.uniform_probTrue`). The final step identifies `learnerFn` with the owned `learnerOf`
  (`learnerOf_eq`, `encodeSample_eq`) and `firstBit ∘ F n k` with `prfConcept F n k`
  (`prfConcept_eq`), giving `predictSuccess (prfConcept F n) m (learnerOf A n m) = acceptProb (F n) D`.

**Edge cases of step 1.** `n = 0`: all statements hold (one point, `firstBit` is `false`).
`m(n) = 0`: the sample is empty (`List.ofFn` over `Fin 0`), the tuple is the single last block.
A fresh point equal to an example: no case distinction, the uniform probabilities range over all
tuples. `A` printing anything other than `[true]`: `learnerFn` is `decide (… = [true])`, as
`learnerOf`. The coins: `B`'s coins are, by `φ`, the `(m(n) + 1)` points (`(m(n)+1)·n` bits, in
`n`-bit blocks) and `A`'s coins (`C`'s coins are `A.coins + 0`, relabelled by `finCongr`).

## 3. Declarations (new, this checkpoint)

- Sample: `foldr_pairEncode_nil`, `firstBit` (`firstBit_eq`), `tupleWord` (`tupleWord_eq`),
  `relabel` (`relabel_eq`, `polyTimeComputable_relabel`), `sampleLen` (`sampleLen_eval`),
  `sampleOf` (`sampleOf_eq`), `lastPair` (`lastPair_eq`, `polyTimeComputable_lastPair`),
  `learnIn` (`learnIn_eq`, `polyTimeComputable_learnIn`), `lastLabel` (`lastLabel_eq`,
  `polyTimeComputable_lastLabel`), `learnIn_tupleWord`, `lastLabel_tupleWord`; private `blk`,
  `length_blk`, `relabel_blk`, `tupleWord_split`.
- Distinguisher: `verdictFun` (`verdictFun_eq`, `polyTimeComputable_verdictFun`),
  `exists_learnDist`; private `zero_add_fun`.
- Law: `iid_uniform`, `predictSuccess_eq_uprob`, `gameProb` (`gameProb_eq`), `learnerFn`
  (`learnerFn_eq`), `snocEquiv` (`snocEquiv_apply`), `exists_learnDist_acceptProb`.

No `@[simp]`, no new `abbrev`.

## 4. Overlap and reuse (this checkpoint; the final report completes the list)

- `learnerFn` restates the owned `learnerOf` (with `encodeSample` unfolded through its reader);
  helper modules cannot import the owned file (it imports them), and Rule 10 makes the owned
  definitions foreign to the helpers. The final proof identifies them by `learnerOf_eq` and
  `encodeSample_eq`. Likewise `firstBit` is the body of `prfConcept` (`prfConcept_eq`).
- `foldr_pairEncode_nil` (`L.foldr pairEncode [] = L.flatMap (pairEncode · [])`): the nearest
  relative is `MultiMsg.encodeHist_eq_flatMap`
  (`Encryption/PrivateKey/FromPRF/ReductionMachine.lean:60`), the same fact for `encodeHist`
  (a fold over typed pairs); not reusable for the sample's fold.
- `sampleOf` restates the body of `MultiMsg.blockMapFun` (`ReductionMachine.lean:229`) for
  `relabel`; `blockMapFun` has no published reader (lint check 8 lists it), so it cannot be
  unfolded under Rule 10. `blk` is `MultiMsg.histBlock` (`ReductionMachine.lean:50`), also
  without a reader, restated privately.
- `iid_uniform` (`(U_X)^m = U_{X^m}`): no relative found (`iid` is used only by the PAC layer).
- Reused: `MultiMsg.exists_queryChain_nuppt`, `flatMap_range_blocks`, `flatMap_ofFn`,
  `length_flatten_of_length`, `histBlockLen`/`eval_histBlockLen`, `GGMRed.pairEncode_append_right`,
  `Rejection.uniform_prod`, `Rejection.uniform_probTrue`, `NUPPT.exists_compParam`,
  `NUPPT.exists_seq`, `ofFn_arrowCongr_finCongr`.
- Imports beyond the brief's list: `Encryption/PrivateKey/FromPRF/ReductionMachine` (upstream of
  `OracleFromPRF`, which the brief lets helpers import), `Pseudorandom/Functions/Asymptotic/GGM/Reduction`
  (imported by the owned file already) and `Randomness/Extraction/Rejection` (imports only
  `InformationTheory`; before the owned module in `order.txt`, so no cycle).

## 5. Scope requests

None.

## 6. Evidence at this checkpoint (`evidence/`, manifest `evidence/SHA256SUMS`)

- `logs/`: `preflight.log`, `source-sha256.log`, `order.txt`, `mathlib-roots.txt`, `cache-store.log`,
  `cache-get.log`, `packages-check.log`, `cache-probe.log`, `bootstrap.log`, `census-bootstrap.txt`,
  `census-bootstrap-vs-base.diff`, `checkpoint1-checks.log` (fresh checks of the three helpers and
  the owned module, status 0; the owned module's one `sorry` warning is the target),
  `checkpoint1-axioms.log` (`propext`, `Classical.choice`, `Quot.sound` for the six step-1 results),
  `base-lint.log` and `checkpoint1-lint.log` (`campaign_style_lint.py TCSlib/Cryptography --check8b`:
  92 FAIL / 101 WARN at both, the same FAIL and WARN line sets), `checkpoint1-width.log` (every line
  ≤ 100 characters, every file ≤ 1000 lines), `checkpoint1-repro.log` (the patch series applied with
  `git am` at the base in a scratch clone, with the committer identity and dates of
  `patches/COMMITS.tsv`, reproduces every hash).
- `probes/`: `CacheProbe.lean`, `AxiomsCP1.lean`.
- `tools/`: the scripts used.

The top-level `SHA256SUMS` lists every delivered file under `inbox/fills/learning/` except itself.
