# Fill dl-a: REPORT (final)

Unit **dl-a** of `briefs/pass-shelat-ch5-8/fills/dl-candidates/brief-issued.md` (the discrete-log
candidates). Owned files: `TCSlib/Cryptography/Candidates/Concrete.lean` and
`TCSlib/Cryptography/Candidates/DiscreteLog.lean`.

- **Base:** `16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1` (the issue commit, head of #210). Local branch
  `fill/dl-a`, created from the base, never rebased, never pushed.
- **Head of `fill/dl-a`:** `70a70a8c235032d6d46da6d7f5078d7de36d2b2e` (8 commits; `patches/` is `git format-patch 16a7d02d..fill/dl-a`).
- **Environment.** Ran as an **internal worker** under the maintainer's environment note
  (`issue/internal-env.md`, which replaces the addendum's Part 1): no preflight floors, no cache
  fetch, no bootstrap. `.lake/packages` is a link to the populated Mathlib tree at the pinned
  revisions; the olean tree `fill-dl-a-oleans` was a full build of the issue commit. At start:
  `nproc` = 4; memory 16.9 GB total, 16.1 GB available (`free -b`); 7.3 GB free on `/`
  (`evidence/logs/start-resources.log`). Never `lake build`, never `lake exe cache get`; one Lean
  process at a time; every module check through `scripts/lean_check_tree.sh`.

## 1. Targets

All seven are **filled**. None partial, none blocked, none escalated.

| # | Target | File | Status | Route |
|---|---|---|---|---|
| 1 | `statClose_rejectBlocksL` | Concrete | filled | the sketch: `rejectBlocksL = (firstHit (E ∘ val) (π r)).map Fin.val` (`rejectBlocksL_eq`, `firstHit_eq`, `List.map_findSome?`, `List.map_coe_finRange`, `List.findSome?_map`, `bitsToNat_eq_listToNat`, `bitsEquiv_val`); `π` pushes uniform to uniform (restriction along the injective block layout, then `Equiv.curry` and `Equiv.piCongrRight bitsEquiv`); `statClose_firstHit`, `StatClose.comp_pushesUniform`, `StatClose.map Fin.val`, `Option.getD_map` |
| 2 | `statClose_sampleBelowL` | DiscreteLog | filled | **corollary**, as ruled (M2): `sampleBelowL_eq_rejectBlocksL`; `statClose_rejectBlocksL (· < m) (Nat.size m) n n` with `d = 0`; `StatClose.comp_equiv_right` along `Fin m ≃ {v : Fin (2^k) // v < m}`; acceptance `m/2^k` by `uprob_comp_equiv`, `bitsEquiv_val`, `uprob_bitsToNat_lt`; `2^k ≤ 2m` by `Nat.lt_size`; `StatClose.mono` |
| 3 | `polyTimeComputable_expSampleRaw` | DiscreteLog | filled | one `polyTimeComputable_iterateFind` loop (see §1.1) |
| 4 | `expSampler_spec` | DiscreteLog | filled | the sketch: case split inside `expGen_runAt` for validity; `sampleBelowL_lt` or the fallback for `v < m`; `expEnc_eq`, `ZMod.val_natCast`; `expDec_expEnc`, `expEval_spec` |
| 5 | `expCollection_sampleClose` | DiscreteLog | filled | `δ n = 1` for `n < n₀` and `(1/2)^n` from `n₀` on (`negligible_two_pow_neg`, `Negligible.mono`); `statClose_sampleBelowL` used directly on the sampler's `n·n` coins (`NUPPT.coinsEquivPoly`, `PolyExpr.eval_mul`/`eval_var`, `finCongr`), mapped through the decoder; the collection read through `Collection.sampleClose_iff`, `expCollection_index`, `expCollection_sample`, `expCollection_decD`, `expCollection_domEquiv` |
| 6 | `expCollection_invProbAt_le` | DiscreteLog | filled | the sketch: `Collection.invProbAt_eq`, `dlProb_eq`; the coins matched by `expCollection_coinsEquiv_uexp`; `OneWay.uexp_mono`, `expCollection_index`; the domain read through `expCollection_domEquiv` (`uprob_comp_equiv`, `expCollection_f`, `expCollection_decD`); `expF_injective`; `decodeFin_eq`, `bitsToNat_eq_listToNat`, `List.ofFn_congr`, `List.ofFn_get` |
| 7 | `expCollection_oneWay` | DiscreteLog | filled | the sketch: `expCollection_sampleClose`, `expCollection_invProbAt_le`, `dlHard_iff`, `Negligible.mono`, `Collection.invProbAt_nonneg`, `dlProb_nonneg` |

`dlCollection_oneWay` ([PS10, Theorem 52.3], not a target) is now sorry-free too (axiom print below).

### 1.1 Where a proof departs from its frozen sketch

- **`polyTimeComputable_expSampleRaw`.** The sketch's ingredients are all used (`H.size` for the
  bit length, `polyTimeComputable_iterateFind`, `polyTimeComputable_pairDropPoly`,
  `polyTimeComputable_pairTakePoly`, the comparison `H.le`, the fallback on `none`). Two
  differences:
  1. **A trial counter.** The loop state is `⟨⟨1^n, ⟨1^k, ⟦m⟧⟩⟩, ⟨counter, coins⟩⟩` and the test is
     "counter nonempty and block `< m`". The sketch's loop without a counter would compute the wrong
     function: the repetition lemma searches `R|x| + 1 ≥ n` rounds, and a block read past the
     end of the coins is `0 < m` and would be accepted, while `sampleBelowL` makes exactly `n`
     trials. (Primality's prime sampler needs no counter because `0` is not prime.)
  2. **Width normalization.** The output is `⟦v⟧_{|p|}` on an arbitrary raw input, where `v` may
     exceed `2^{|p|}`. It is computed as the last `|p|` bits of `⟦p − p⟧_{|p|} ++ block` (`H.sub`,
     `polyTimeComputable_pairDropPoly`, `PolyTimeComputable.append`), not by
     `polyTimeComputable_unaryPoly`/`polyTimeComputable_blockMap` as the sketch suggests: no
     pad-with-zeros primitive is in scope, and `⟦0⟧_W = subStr ⟨p, p⟩` comes from the bundle itself
     (no new bundle field is needed).
- **`expCollection_sampleClose`.** As the brief says, `statClose_sampleBelowL` is applied directly;
  its own proof carries the `firstHit`/`chunk` argument of this sketch.
- The sketches are frozen, so these notes are here. A sketch refresh for
  `polyTimeComputable_expSampleRaw` is suggested at the next docstring window.

## 2. New private declarations (all `private`, prefix `dla_`)

**`Concrete.lean`** (helpers of `statClose_rejectBlocksL`):

| Name | Role |
|---|---|
| `dla_pushesUniform_restrict` | restricting a uniform table `I → Bool` along an injection `α → I` is uniform (the first projection of the split of `I` into the range and its complement) |
| `dla_blockPos` | the coin position `t·B + j` of bit `j < k` of block `t` |
| `dla_blockPos_injective` | it is injective |
| `dla_take_drop_ofFn` | `((ofFn r).drop (t·B)).take k = ofFn (the first k bits of block t)` |

**`DiscreteLog.lean`**, helpers of `polyTimeComputable_expSampleRaw` (under the section header
"The domain sampler as a trial loop"):

| Name | Role |
|---|---|
| `dla_listToNat_append` | `⟦a ++ b⟧ = ⟦a⟧·2^{|b|} + ⟦b⟧` |
| `dla_listToNat_nil` | `⟦[]⟧ = 0` |
| `dla_drop_natToList_zero_append` | width normalization: `(⟦0⟧_W ++ b).drop |b| = ⟦⟦b⟧⟧_W` |
| `dla_findSome?_ite` | `findSome?` of a filter-and-map is `find?`, then `map` |
| `dla_find?_range_lt` | a search over `[0, L)` whose test demands `i < N` is the search over `[0, N)` |
| `dla_ssStart`, `dla_ssStep`, `dla_ssBlock`, `dla_ssAcc`, `dla_ssOut` | the loop's start state, step, trial value, test and payload: instance data for the public host `polyTimeComputable_iterateFind` (no new host) |
| `dla_ssStart_poly`, `dla_ssStep_poly`, `dla_ssBlock_poly`, `dla_ssAcc_poly`, `dla_ssOut_poly` | their polynomial time |
| `dla_ssStep_iterate`, `dla_length_ssStep_le`, `dla_length_ssStep_ssStep_le`, `dla_length_ssStep_iterate_le` | the orbit and the orbit bound `2|x| + 4` |
| `dla_ssFind_eq` | the loop computes `sampleBelowL m (Nat.size m) n n r` with the fallback `0` |

Helpers of `expCollection_sampleClose`: `dla_statClose_one` (any two samplers are `1`-close) and
`dla_statClose_expDec` (the decoded sampler is `(1/2)^n`-close to uniform on `Z_m` at a valid index
of width `n`). Helper of `expCollection_invProbAt_le`: `dla_dl_of_inv` (an inversion success is a
discrete-log success at a valid index).

**Authorized re-points: none.** The brief has no dl-a re-point item, and no non-target proof was
touched.

## 3. Reuse-not-copy screen (duplicated material, for approval)

| Helper | Relation | Request |
|---|---|---|
| `dla_pushesUniform_restrict` | generalizes `TCSlib.Cryptography.pushesUniform_comp_injective` (`Asymptotic/MultiMessage.lean`, public but outside the order list, domain fixed to `Fin (q+1)`) and copies its proof architecture (`Equiv.ofInjective`, `Equiv.Set.sumCompl`, `Equiv.sumArrowEquivProdArrow`), at `O = Bool` with any finite domain (about 15 lines) | promote a generic `HardcoreBit.pushesUniform_restrict` (any finite domain, any nonempty codomain) to `HardcoreBit/Basic.lean`; `MultiMessage` and this proof would both cite it |
| `dla_listToNat_append` | the fold identity of the **private** `foldl_bits_eq` of `Asymptotic/Sampling.lean`, re-proved (about 12 lines) | publish `listToNat_append` beside `listToNat` (`NumberTheory/Primality.lean`) |
| `dla_blockPos`, `dla_take_drop_ofFn` | close to `NumberTheory.chunk` and its **private** `ofFn_chunk` (`Primality.lean`), but reading the first `k ≤ B` bits of each block | publish `ofFn_chunk` (with a `take` form), so that the block readers of `rejectBlocksL` and `samplePrime` share one lemma |
| `dla_ss*` loop family | the pattern of Primality's private `spStep`/`spAcc`/`spOut` (a different loop: a counter, and a `k`-bit block of an `n`-bit stride) | a public "block rejection loop" instance of `iterateFind` would serve `sampleBelowL`, `rejectBlocksL` (RSA, Rabin) and `samplePrime`: suggested for the construction registry |
| `dla_findSome?_ite`, `dla_find?_range_lt`, `dla_statClose_one` | generic list and probability facts; no lemma of this form found in the closure | none, or promote with the above |

**Mathlib first:** dl-a needs no number theory (`mathlib-overlap-nt.md`, "Advice"). The bit-length
facts are Mathlib's `Nat.size_le`, `Nat.lt_size_self`, `Nat.lt_size` and `Nat.size_pos`.

## 4. Missing equations; name corrections

- **No E-API.** Every foreign definition was read through a published lemma.
- **No name correction** beyond the brief's table (dl-a had none).
- **Notes for the maintainer.**
  - Unification can unfold a foreign definition where the lexical grep sees nothing; the seal
    catches it. Two cases met here: `polyTimeComputable_not (H.le.comp …)` elaborates by unfolding
    `leStr`, so it is restated through `leStr_pairEncode` first; and
    `rw [← expCollection_coinsEquiv_uexp …]` matched the *collection's* average by unfolding the
    coin types, so it is applied with `le_of_le_of_eq` to the right-hand side. Fill briefs could
    warn about both patterns.
  - A `match` produced by `polyTimeComputable_iterateFind`'s statement and one written in a helper
    use different auxiliary matchers, so `rw` cannot equate them; the helper `dla_ssFind_eq` is
    applied by `congrArg … |>.trans` (definitional equality of the two matchers, which are not
    TCSlib definitions).

## 5. Checks

### 5.1 Owned files and sweep

- Each owned file checks with **0 errors and 0 warnings** at the head (no `sorry` in either):
  `Concrete` 6 s; `DiscreteLog` 13–15 s per check (`evidence/logs/module-checks.log`, every check
  with its start and end time).
- **Sweep** of the whole order list (`inputs/dl-a/order.txt`, 94 modules, in order, through
  `scripts/lean_check_tree.sh`): **SWEEP OK**, all 94 modules passed with 0 errors (`SWEEP OK: all modules passed, end 2026-11-06T12:37:46+00:00`; started 2026-11-06T12:28:26+00:00). Log: `evidence/logs/sweep.log`.
- **Sorry census from the sweep** (warnings `declaration uses 'sorry'` per module, against
  `inputs/dl-a/base-sorries.txt`): **71 sorries in 13 modules**: the base's 78 in 15 modules minus exactly this unit's 7 (the `Candidates/Concrete` and `Candidates/DiscreteLog` rows are gone); every other row equals its base count.

```
      2 TCSlib/Complexity/ClassP/TimeConstructible
      1 TCSlib/Complexity/Randomized/NonUniform
      5 TCSlib/Complexity/TuringMachine/Build/Loop
      3 TCSlib/Complexity/TuringMachine/Build/Primitives
      2 TCSlib/Complexity/TuringMachine/Build/Wrappers
      3 TCSlib/Complexity/TuringMachine/Composition
      1 TCSlib/Complexity/TuringMachine/Encoding
      1 TCSlib/Complexity/TuringMachine/Simulation
      7 TCSlib/Cryptography/Candidates/DiscreteLogHardcore
      7 TCSlib/Cryptography/Candidates/ElGamal
     10 TCSlib/Cryptography/Candidates/Factoring
     10 TCSlib/Cryptography/Candidates/RSA
     19 TCSlib/Cryptography/Candidates/Rabin
```

### 5.2 Axiom prints (`evidence/logs/axioms.log`)

```
'TCSlib.Cryptography.Candidates.statClose_rejectBlocksL' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.statClose_sampleBelowL' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_expSampleRaw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.expSampler_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expCollection_sampleClose' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expCollection_invProbAt_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expCollection_oneWay' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlCollection_oneWay' depends on axioms: [propext, Classical.choice, Quot.sound]
[probe exit 0, 7 s]
```

### 5.3 Rule-10 seal (`evidence/seal/`, `evidence/logs/seal.log`)

- **Sealed copies** `SealedConcrete.lean` and `SealedDiscreteLog.lean` (made by
  `evidence/seal/mkseal.py`): each owned file, with every helper group and target wrapped in
  `section dlaSeal … end dlaSeal` carrying `attribute [local irreducible]` on the foreign
  definitions. The seal is scoped to the fill's code because a whole-file seal also breaks two
  pre-existing non-target proofs, which are not this unit's and were not touched: in `Concrete`, a
  `subtypeEquiv` reading of `bitsEquiv` near line 339; in `DiscreteLog`,
  `ExpGroupGen.FullLength.exists_fullLengthExcept` (a lambda for `Negligible`).
- **Sealed names, `Concrete`:** `StatClose uprob uexp firstHit bitsToNat bitsEquiv
  NumberTheory.listToNat HardcoreBit.PushesUniform`.
- **Sealed names, `DiscreteLog`:** `Candidates.rejectBlocksL StatClose uprob uexp firstHit bitsToNat
  bitsEquiv NumberTheory.listToNat HardcoreBit.PushesUniform Candidates.natToList Candidates.sizeStr
  Candidates.subStr Candidates.leStr decodeFin Turing.pairEncode Complexity.pairFstD
  Complexity.pairSndD Complexity.PolyTimeComputable Complexity.PolyExpr.eval NUPPT.inArg
  NUPPT.inParam NUPPT.inCoins NUPPT.coinsEquivPoly NUPPT.coinsCongr NUPPT.runAt NUPPT.runAtL
  NUPPT.coinLen NUPPT.ofPolyTimeUniform Collection.SampleClose Collection.invProbAt Collection.index
  Negligible`. Full names: `evidence/seal/*-sealed-names.txt`. None is `@[simp]`, so no
  `attribute [-simp]` is needed. `NUPPT.Coins` is a reducible `abbrev`, which is notation and cannot
  be sealed (policy §1).
- **Result:** both sealed copies compile with **0 errors and 0 warnings**.
- **Controls:** `firstHit E xs = (List.finRange T).findSome? … := rfl` (Concrete) and
  `rejectBlocksL (· < m) k B T r = sampleBelowL m k B T r := rfl` (DiscreteLog) each **close
  unsealed and fail sealed** ("Type mismatch: rfl"); `evidence/seal/controls.out`.
- **The seal found one real issue**, fixed in commit `70a70a8c`: `rw [PolyExpr.eval_const]` had
  rewritten only the first constant of the orbit polynomial, and `(const 4).eval` closed by defeq.
- **Grep of the diff** for foreign definition names inside `simp`, `simp only`, `rw`, `unfold`,
  `dsimp` and `delta` lists (`evidence/seal/grep-foreign.txt`): 109 tactic lists scanned, and **no
  foreign definition is used as a rewrite or unfold rule** (the result is empty). The three lexical
  hits are arguments or type ascriptions inside lemma terms: `uprob_comp_equiv (bitsEquiv …)`, a
  `show … from` term that mentions `listToNat`, and `Equiv.refl (A.Coins n)`. Every `unfold`
  names an own-file definition (`sampleBelowL`, `expSampleRaw`, `dlW`, `expSampler`).

### 5.4 Lint (`evidence/logs/lint.log`)

`python3 scripts/campaign_style_lint.py TCSlib/Cryptography/Candidates`: `style_lint: 8 FAIL, 9 WARN
over 8 files`. **No FAIL in the owned files' rows.** The FAILs are Rabin's seven and ElGamal's
`polyTimeComputable_egGroupGenRaw`, both pre-existing and not this unit's. The owned files' rows:

- `WARN DiscreteLog.lean 1426 lines > 1000`: **new with this fill** (973 lines at the base). The
  statement freeze and the file ownership leave no legal split here; the poly-time machine (about
  290 lines) is most of the growth. **I request a size exception or a post-fill split**, for
  example the trial-loop section into `Candidates/DiscreteLogSampler.lean`.
- `WARN DiscreteLog.lean 6 public def(s) without a lemma beside them (check 8)`: pre-existing,
  unchanged.
- `INFO Concrete.lean 689 lines > target 600` (590 at the base).

## 6. Diff and delivery

- The diff touches only the two owned files: `2 files changed, 559 insertions(+), 7 deletions(-)`. The only removed lines are the seven
  `  sorry`. Statement freeze verified mechanically: each base file, minus its `sorry` lines, is a
  line subsequence of the head file.
- Delivered as `inbox/fills/dl-a/` on `exchange/pass-shelat-ch5-8` (`REPORT.md`, `patches/`,
  `src/`, `evidence/`): checkpoints 1 and 2, then `fill dl-a: final`.
