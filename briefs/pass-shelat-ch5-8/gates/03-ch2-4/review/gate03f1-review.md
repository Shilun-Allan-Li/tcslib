# Gate 03f1: review of the auditor's findings (discrete log, its hard-core bit, El Gamal, the samplers)

- **Reviewed:** `briefs/pass-shelat-ch5-8/gates/03-ch2-4/findings/gate03f1-findings.md`: 148 rows (1 major, 2 minors, 145 notes) and 21 sorry verdicts (15 (a), 6 (b), 0 (c)).
- **Code:** worktree `SP/wt-g03c-fix` at `0c348ff94cacf24d96d99078c9dd9e328530c8d2` (checked with `git rev-parse HEAD`). Line numbers below refer to that commit. `SP` = `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.
- **Since the pin.** #203, #204 and #205 have merged (head `ee6a8d02`). None touches `Candidates/{DiscreteLog, DiscreteLogHardcore, ElGamal, Concrete, Arithmetic}.lean` or the DL fill brief (`git diff 0c348ff9 HEAD`). `inventory-ch2.md` changed only in its Miller–Rabin rows (gate 03f2, F01–F02). The Claim-62.2 rows of finding 2 are unchanged. **No finding is affected by them.**
- **Downstream code read:** prong A `SP/wt-prong-a` at `2d7b5441` (`Authentication/DLHash.lean`). I grepped prongs B, C, D, D2 and S2b (`587843c7`, `9e6f08bb`, `6ea900ae`, `c6198d86`, `afe5982f`, `27ae72da`) for every declaration of this pack. Only the facade `Candidates.lean` and prong A's `DLHash.lean` mention them.
- **Source:** `blueprint/src/references/pass-shelat-2010-ch3.raw.md` (§3.4.1 pp. 84–86, §3.11 pp. 105–107) and `-ch2.raw.md`.
- **Records:** DESIGN §5 items 20–21, §8 item 3; run-3 summary P8-1 to P8-3; the inventories; `fills/dl-candidates/brief-draft.md`; gate 03f2's findings (row D148).
- **Not done.** No Lean was built or run. The finite checks were exact rational arithmetic and exhaustive enumeration in `SP/g03rev2/f1check.py`, run with `python3 -I`.

## Summary

- **Verdicts on the three findings: 3 true, 0 partly true, 0 false.**
  - #1 is true and slightly understated: the sketch has four further slips (§1.3).
  - #3 is true, but its line references are off: the text is at `ElGamal.lean:57–62` and `:295–298`, not `:49` and `:294`.
  - I spot-checked the notes, re-deriving every constant they state. None is false.
  - **I agree with all 21 sorry verdicts (15 (a), 6 (b), 0 (c)), and the counts reconcile** with `evidence/f1/admissions.txt` (21) and `axioms.log` (150 prints, 34 `sorryAx`; 124 in the four files plus 26 in `Arithmetic.lean`).
- **The most important answer: `fullDLCollection_hardCore` stays provable as stated.** Only its proof sketch is wrong (§1.2 gives the corrected one). No statement in the pack is false, unprovable, or weaker than its docstring claims. One hypothesis, `hbig`, is stronger than needed (M1).
- **Severity changes: none.**
  - #1 stays **major**. The fill brief tells workers "Each target's docstring carries its proof sketch. **Follow it, or report why it fails**" (`fills/dl-candidates/brief-draft.md`). The sketch describes a coin budget on which its own 2⁻ⁿ sampling claim is false (exhaustive counterexample below). That is "materially misleading" for the fill it gates, even though the fix is to a docstring.
  - #2 stays **minor** (records), and #3 stays **minor** (docstring).
- **Fixes, in order of importance:**
  1. **#1.** Replace the second half of `fullDLCollection_hardCore`'s sketch (`DiscreteLogHardcore.lean:561–579`) by the text in §1.4. This is a docstring change only, and it must land before the dl-b fill is issued.
  2. **M2.** `sampleBelowL m k B T` is definitionally `rejectBlocksL (· < m) k B T`. Derive `statClose_sampleBelowL` from `statClose_rejectBlocksL` (re-point its sketch and the fill brief). Otherwise dl-a fills the same lemma twice.
  3. **M3.** Drop the stale "requested shared primitive" phrases at `DiscreteLog.lean:517` and `ElGamal.lean:512–513`. `H.size` and `H.sub` are bundle fields (P7-1). Under the fill brief's "report any missing operation" rule, the phrases would trigger spurious reports.
  4. **#3.** Correct the P8-1 history at `ElGamal.lean:57–62` and `:295–298`, aligning it with DESIGN §5 item 20.
  5. **M1.** Change "Needed"/"must have" for `hbig` at `DiscreteLog.lean:51–52, :319–321` and `ElGamal.lean:845–847` to "used". The hypothesis is dispensable in both headline theorems.
  6. **#2.** Records: move Claim-62.2 to `Rabin.lean · rabin_symmetry` in `inventory-ch2.md:194, 445, 517`.
  7. **M4.** Records: the pack's interface-use note under-lists what ch. 5–8 uses (prong A's `DLHash.lean`).
- **Rulings needed: none.** Every recommended fix is a docstring or records change, with no statement or interface change and no debt. One *optional* ruling, R-03f1-1 (drop `hbig` from the two headline theorems, M1), is set out in §M1. Under the recommended option A it is not needed.
- **Ripple:**
  - No other gate-03 pack is affected.
  - In ch. 5–8, prong A's `DLHash.lean` uses `ExpGroupGen`, `ExpGroupGen.DLHard`, `ExpValid`, `dlM`, `dlP`, `expGenFun`, `expSampleRaw`, `expEval`, `expF_injective` and `statClose_sampleBelowL`. None of the fixes changes any of them. M2 adds a lemma and keeps `sampleBelowL`'s definition.
  - `Checks.lean`: no change.

---

## 1. Finding #1 (major): the random-tape and statistical-error calculation in `fullDLCollection_hardCore`'s sketch

### 1.1 Verdict: **true**. Severity: **major (agree)**.

**What the sketch says** (`DiscreteLogHardcore.lean:562–579`):
- `s := ⌊ε(p−1)/4⌋`, `T := ⌈(p−1)/s⌉ ≤ 8n^c + 1`, `k := n`, `ℓ := 4n·(2n^c)² = 16n^{2c+1}`, with `ε = n^{-c}/2`.
- Coins `T·n + n·ℓ·(2n + A.coins)`.
- "samples `t` and the `r_{j,i}` by rejection (`sampleBelowL` with `H.le`; the statistical term `n·ℓ·(1/2)^n + (1/2)^n` by `statClose_rejectionSample`/`StatClose.prod` …)".
- Conclusion: `G.dlProb B n ≥ 3ε/(8(8n^c+1)) − 2n^{2c+2}(1/2)^n`.

**Each of the auditor's three claims checks:**
1. **A `2n`-bit block cannot carry a rejection sample within 2⁻ⁿ of uniform.**
   - The only closeness lemma for `sampleBelowL` is `statClose_sampleBelowL` (`DiscreteLog.lean:499–502`). It is for `sampleBelowL m (Nat.size m) n n` on `Fin (n * n) → Bool`, that is n trials of n-bit blocks, n² coins.
   - On `2n` coins the third block is `drop (2n) r = []`, and `listToNat [] = 0 < m`, so after two rejections the sampler outputs 0.
   - I enumerated all 2²⁰ tapes for `p = 523` (prime, `523 ≡ 3 mod 4`, `2⁹ ≤ 523 < 2¹⁰`), `n = 10`, `m = 522`, `k = Nat.size 522 = 10`.
     - The distance from uniform on `[0, 522)` is exactly **32823521/136839168 ≈ 0.23987**. This is `(1 − 522/1024)²(1 − 1/522)`, the auditor's value.
     - The claimed bound is `2⁻¹⁰ ≈ 0.00098`.
     - With n² = 100 coins the same formula gives `(502/1024)¹⁰(521/522) ≈ 0.00080 ≤ 2⁻¹⁰`, as `statClose_sampleBelowL` says.
   - Rejection over a single block cannot reach 2⁻ⁿ either: two trials of n bits fail with probability up to 1/4.
2. **The final coefficient is wrong.** With the sketch's own `ℓ = 16n^{2c+1}`, the statistical term it names is `nℓ·2⁻ⁿ + 2⁻ⁿ = (16n^{2c+2} + 1)2⁻ⁿ`, not `2n^{2c+2}2⁻ⁿ`. Both are negligible, so the contradiction survives, but the displayed bound is false as written.
3. **`T·n` is not a coin polynomial.** `T = ⌈(p−1)/s⌉` depends on the input's `p`, while `NUPPT` coins are a `PolyExpr` in `n`. The budget must use a bound `K(n) ≥ T`, and t must be sampled below the input-dependent `T` from a fixed-size block.

### 1.2 Is the statement still provable as stated? **Yes.**

I re-derived the whole chain against the code. The statement (`:580–582`) needs no change:
- `Collection.HardCore` (`Collections.lean:229–236`) is one-sided: `≤ 1/2 + ε(n)` for every n, averaged over `Gen`'s coins with an ideal uniform x.
- `halfPred` is exactly balanced at every valid index: `p − 1` is even, so `#{x < p−1 : 2x+2 ≤ p} = (p−1)/2`. A constant predictor therefore gets exactly 1/2. The source's inclusive `half` would be biased by `1/(p−1)`.
- The concrete lemmas, re-derived:
  - **`uprob_trial_ge`.** The disagreement sets have sizes `2e` and `2d`, both `< 2s`, and `4s ≤ ε(p−1)` gives a loss of at most `ε/2`.
  - **`uprob_majOracle_ne_le`.** `HardcoreBit.majority` sends ties to `false` (`PairwiseIndependence.lean:235`). A wrong majority forces at most ℓ/2 correct votes. Chebyshev then gives `(ℓ/4)/(ℓε/2)² = 1/(ε²ℓ)`.
  - **`invProb_shiftInverter_ge`.** `invProb` is the preimage form, `Experiments.lean:60`. The guess `t = ⌊e/s⌋ < T` has probability `1/T`. An empty coin type gives `δ ≥ 1`.
  - **`invProb_dlInverter_ge`.** Use a union bound over the k rounds at the *perfect-path* queries `±g^{⌊e_j/2⌋}`. These lie in the two windows, because `ε ≤ 1/2` forces `s ≤ (p−1)/8`. Off the union, the noisy path equals the perfect path, so `dlLoop_eq_dlBits` applies.
  - **`dlBits_pow`.** For even e the kept root is `g^{e/2}`, because the other root `g^{e/2+(p−1)/2}` has `2·val ≥ p−1`. For odd e use `g^{e−1}`. The base case is k = 0, e = 0.
- The asymptotic wrapper works with the parameters of §1.4. All the arithmetic it needs is in `ArithmeticFP`: `sub`, `add`, `divMod`, `le`, `modExp`, `xgcd`, `mul`. The loops it needs are in the closure calculus: `polyTimeComputable_iterateFind`, `_iterateEmit`, `_majority`, `NUPPT.polyTimeComputable_layout`.

### 1.3 What the auditor did not say (further slips in the same sketch)

1. `:561`: "`A_i y ρ := A.distinguisherL n ⟨i, encD y⟩ ρ`" is a type slip. `encD` encodes domain elements of `Z_{expOrd i}`, and `y` is a unit. The predictor sees `f_i(x)`, so it should be `A_i y ρ := A.distinguisherL n (pairEncode i (natToList n (y : ZMod p).val)) ρ`.
2. `:570`: `statClose_rejectionSample` is the typed sampler on `Fin T → Fin k → Bool`. The string sampler the machine runs is covered by `statClose_sampleBelowL`, which this fill then depends on (fill order: dl-a first).
3. `:563`: "`T ≤ 8n^c + 1`" needs `p − 1 ≥ 8n^c(8n^c + 1)`, not only the stated `p − 1 ≥ 8n^c`.
   - With `x = (p−1)/(8n^c)` and `s = ⌊x⌋ ≥ x − 1`, `(p−1)/s ≤ 8n^c/(1 − 8n^c/(p−1))`.
   - This is true for large n on full-length p, but the sketch should say so, or use a cruder bound.
   - My bound: if `x ≥ 2` then `s ≥ x/2`, so `T ≤ 16n^c`. The auditor's `K(n) = 16(n+1)^c + 1` is looser and also correct.
4. `:568`: "computes `s` and `T` from `1^n` and `p` (`H.divMod`, `H.mul`)" needs the binary numeral of `8n^c`.
   - Neither the bundle nor the candidates' closure calculus converts unary to binary. `H.size` goes the other way.
   - Two routes exist:
     - put the n-bit numeral of `8n^c` in B's advice (B is non-uniform, and `DLHard` quantifies over every `NUPPT`);
     - or build it from main's `countLoop` (`ClassP/BinaryArith/PrimeFind.lean:144`, `Nat.bits |z|`) and `polyTimeComputable_reverse` (`BinaryArith/Mul.lean:73`), with a glue lemma between the two numeral conventions.
   - The advice route is cheaper. This is not a missing bundle field, because the statement does not need one.

### 1.4 Concrete fix: the corrected sketch (replace from "Apply `invProb_dlInverter_ge` …" at `:562` to the end of the docstring at `:579`; also fix `:561`)

```text
success is `predProb (expo g_u) (halfBit (p−1)) A_i` with
`A_i y ρ := A.distinguisherL n (pairEncode i (natToList n (y : ZMod p).val)) ρ`.
Apply `invProb_dlInverter_ge` with `ε := n^{-c}/2`, `s := ⌊(p−1)/(8n^c)⌋` (so `4s ≤ ε(p−1)`),
`T := ⌈(p−1)/s⌉` (so `Ts ≥ p − 1`), `k := n` (`s ≤ p − 1 < 2^n`) and `ℓ := 16 n^{2c+1}`
(so `k/(ε²ℓ) = 1/4`). For large `n` the good instances have `p − 1 ≥ 2^{n−1} − 1 ≥ 16 n^c`, so
`(p−1)/(8n^c) ≥ 2`, `s ≥ (p−1)/(16 n^c) ≥ 1` and `T ≤ K(n) := 16 n^c < 2^n`; the inverter then
succeeds with probability `≥ (3/4)/T ≥ 3/(4K(n))` on each good instance, with ideal coins.
The machine `B` realising `dlInverter` is a non-uniform PPT: advice `⟨A.advice n, ⟦8n^c⟧_n⟩`
(the `n`-bit numeral of `8n^c`: the bundle has no unary-to-binary conversion); coins
`n·n + n·ℓ·(n·n + A.coins)` (a `PolyExpr`, `c` being fixed): one block of `n·n` coins for `t`
and, for each of the `n·ℓ` trials, a block of `n·n` coins for `r_{j,i}` and `A.coins` coins for
`ρ_{j,i}`. On `⟨1^n, ⟨i, y⟩⟩` it reads `p`, `g` from `i`; computes `s` and `T` (`H.sub`,
`H.divMod`, `H.add`); outputs `0^n` unless `1 ≤ s` and `T < 2^n` (the analysis uses only the good
instances); samples `t := (sampleBelowL T (Nat.size T) n n ·).getD 0` and
`r_{j,i} := (sampleBelowL (p−1) (Nat.size (p−1)) n n ·).getD 0` (`H.le`, `H.size`,
`polyTimeComputable_iterateFind`); shifts `y · g^{−ts}` (`H.modExp`, `H.xgcd`); and runs the `n`
rounds of `dlLoop` (`Complexity.polyTimeComputable_iterate` with the state `⟨y_j, bits⟩`, D11):
quadratic residuosity by `H.modExp` (`y^{(p−1)/2} = 1`, Euler), the root `y^{(p+1)/4}` by
`H.modExp` (`sqrtMod3`, [PS10, Theorem 58.2]), the `ℓ` oracle calls `A.output` on the layout
`⟨⟨⟨1^n, ⟨i, z_{j,i}⟩⟩, A.advice n⟩, ρ_{j,i}⟩` (`polyTimeComputable_iterateEmit`,
`NUPPT.polyTimeComputable_layout`), the comparison with `half(r_{j,i})` (`halfStr`), the majority
(`polyTimeComputable_majority`), the negation `p − z` and the bit assembly; finally
`(bits + ts) mod (p−1)` as an `n`-bit numeral (`decodeFin n` reads it back,
`bitsToNat_natToBits`). Sampling: each of the `1 + nℓ` sampled coordinates is within `(1/2)^n`
of uniform (`statClose_sampleBelowL`, with `0 < T < 2^n` and `0 < p − 1 < 2^n`); the coins of `A`
are exact; `StatClose.prod` and `StatClose.abs_uprob_sub_le_prod` give a loss of at most
`(1 + 16 n^{2c+2})(1/2)^n` at every instance. Averaging over the good set (probability
`≥ ε/2`, `HardcoreBit.uprob_mul_le_uexp`):
`G.dlProb B n ≥ (ε/2)·3/(4K(n)) − (1 + 16 n^{2c+2})(1/2)^n = 3/(256 n^{2c}) − (1 + 16 n^{2c+2})(1/2)^n`
for infinitely many `n`, an inverse polynomial, contradicting `hDL B` via `not_negligible_iff`.
```

**Alternative (not recommended).** Keep `2n`-bit exponent blocks and reduce modulo `p − 1`. The distance is `r(m−r)/(2^{2n}m) ≤ m/2^{2n+2} < 2⁻ⁿ/4` (`r = 2^{2n} mod m`; ≈ 8.9·10⁻⁵ for the example above). This needs a new sampling lemma that the library lacks, and the machine would differ from `expSampleRaw`'s sampler.

**Ripple.**
- `DiscreteLogHardcore.lean` docstring only. No statement, `Checks.lean` or other-pack change.
- In ch. 5–8 nothing changes: no prong cites `fullDLCollection_hardCore` (grep, all prong worktrees).
- The dl-b fill brief must be issued after this fix. It should cite `statClose_sampleBelowL` as a dependency, which makes dl-a's sampler lemma a prerequisite of dl-b's headline.

---

## 2. Finding #2 (minor): Claim-62.2's location

### Verdict: **true**. Severity: **minor (agree)**.

- `inventory-ch2.md` gives `Concrete.lean` in three places:
  - `:194`, the row's location column;
  - `:445`, "New concrete lemma in `Candidates/Concrete.lean`";
  - `:517`, item C6 under "§4 New concrete-layer lemmas … put these in `Concrete.lean` unless noted".
- The lemma is `Candidates/Rabin.lean:198`, `rabin_symmetry`, at the pin and at head. `Concrete.lean` has no Claim-62.2 statement.
- DESIGN §6 (`DESIGN.md:1142`) already assigns Claim-62.2 to Cand2 (RSA/Rabin).
- 03f1's pack lists Claim-62.2 in its source list (`03f1-pack.md:23`) and in its inventory scope (`:57`), so it was mis-scoped to this pack.
- **The coverage gap the auditor raises does not exist.** Gate 03f2, whose scope includes `Rabin.lean`, audited it (`gate03f2-findings.md` row D148, a note: faithful). 03f2 closed at 0 majors.

**Fix (records).**
- `inventory-ch2.md:194`: change the location to `Cryptography/Candidates/Rabin.lean` (`rabin_symmetry`).
- `inventory-ch2.md:445`: replace "New concrete lemma in `Candidates/Concrete.lean`" by "In `Candidates/Rabin.lean` (`rabin_symmetry`)".
- `inventory-ch2.md:517`: "C6 Claim-62.2 (Rabin symmetry lemma), in `Candidates/Rabin.lean`".
- In `resolutions-03f1-r1.md`, record that the item belongs to 03f2 (D148).

**Ripple:** none.

---

## 3. Finding #3 (minor): the P8-1 history overstates when the old definitions made DDH false

### Verdict: **true**. Severity: **minor (agree)**. The line references are wrong: use `ElGamal.lean:57–62` and `:295–298`.

**Check.**
- On the old seed `Σ r, Z_{q_r}^k` (k = 2 or 3), the coin string r has weight `q_r^k / Σ q^k`.
  - **Constant q:** both weights are `2^{-|r|}`, so the instance laws coincide. "false for every randomized generator" (`:61–62`) is therefore false.
  - **q varying on a negligible set** (say one coin string `r₀` out of `2^{L(n)}`): both laws put mass at most `2/(2^L − 1)` off the common value, so they are negligibly close. "false for every generator whose `q` varies with the coins" (`:298`) is therefore false too.
  - **Non-negligible variation:** two same-length orders `q`, `3q/2` on half the coins each give the instance laws `(4/13, 9/13)` and `(8/35, 27/35)`, at distance `36/455`. Here the threshold test works.
- DESIGN §5 item 20 already words this correctly: "uniform-on-Σ tilts the instance law by the fibre sizes".
- The repair (product seeds) is right and must stay.

**Fix (docstrings).**
- `ElGamal.lean:59–62`. Replace "— the two ensembles then had different instance laws whenever `q` varies with the coins, and the threshold test `[q ≥ θ_n]` distinguished them with constant advantage, so `DDHAssumption` was false for every randomized generator." by:

  > — so the two ensembles could have different instance laws, and when `q` varies non-negligibly with the coins (two orders `q`, `3q/2` on half the coins each give the laws `(4/13, 9/13)` and `(8/35, 27/35)`) a threshold test `[q ≥ θ_n]` distinguished them, making `DDHAssumption` false for reasons unrelated to DDH.

- `ElGamal.lean:297–298`. Replace "making `DDHAssumption` false for every generator whose `q` varies with the coins." by "which could make `DDHAssumption` false for reasons unrelated to DDH (DESIGN §5 item 20)."

**Ripple:** none.

---

## 4. The 21 admitted declarations (verdict of the auditor → mine)

| File · declaration | Auditor | Mine | Reason (re-derived) |
|---|---|---|---|
| `DiscreteLog` `statClose_sampleBelowL` :499 | a | a | Law `(1−λ)U + λδ₀`, `λ = (1−m/2^k)^n ≤ 2⁻ⁿ` (`2^{k−1} ≤ m`), exact distance `λ(1−1/m)`. Also a corollary of `statClose_rejectBlocksL` (M2). |
| `polyTimeComputable_expSampleRaw` :522 | a | a | A total function. Bit length by `H.size` (stale wording, M3), comparisons by `H.le`, `iterateFind`, padding. |
| `expSampler_spec` :549 | a | a | Valid at every n (`G.valid`/`hV` from `n₀` on, `expValid_dlDefaultIndex` below). `v < m < p < 2^{dlW}` decodes canonically. |
| `expCollection_sampleClose` :618 | b | b | `δ = 1` below `n₀`, `2⁻ⁿ` above. True. D10 sampling relaxation (declared). |
| `expCollection_invProbAt_le` :635 | a | a | `expF_injective` plus canonical `expDec` give width n and value `x.val`. `decodeFin`/`bitsToNat_eq_listToNat` share the MSB-first convention (`Primality.lean:660`). |
| `expCollection_oneWay` :647 | b | b | Follows from the previous two. D10. |
| `DiscreteLogHardcore` `dlBits_pow` :319 | b | b | True (§1.2). Restricted to `p ≡ 3 (mod 4)` (declared, DESIGN §8 item 3). |
| `uprob_trial_ge` :357 | a | a | §1.2. `p = 2` and empty `ρ` make the hypotheses infeasible. |
| `uprob_majOracle_ne_le` :380 | a | a | §1.2 (ties to `false`, Chebyshev). |
| `invProb_shiftInverter_ge` :408 | a | a | §1.2. |
| `invProb_dlInverter_ge` :435 | a | a | §1.2 (perfect-path union bound). |
| `polyTimeComputable_halfStr` :526 | a | a | `2x+2 ≤ p ⟺ x < ⌊p/2⌋`: `H.divMod`, `H.le`, negation. |
| `fullDLCollection_hardCore` :580 | b | b | Provable as stated (§1.2). Narrower than the source by `p ≡ 3 (mod 4)` and D10. Its sketch is wrong (#1). `hbig` is avoidable (M1). |
| `ElGamal` `statClose_sq_generator` :220 | a | a | TV(uniform on `G_q`, uniform on `G_q∖{1}`) is exactly `1/q`, attained at `{1}`. `q ≥ 2` keeps the subtype nonempty. |
| `polyTimeComputable_egGenRaw` :515 | a | a | Total function. On `p ∈ {0, 1}` the sampler falls back to `g = 1`. Stale wording, M3. |
| `polyTimeComputable_egEncRaw` :565 | a | a | Total function. On `p = 0` the n-bit truncation is `modExp` modulo `2^n` (the auditor's point holds). |
| `egDecStr_apply` :626 | a | a | `xgcdStr`'s inverse has width `|p|`, `mulStr` is lossless and `divModStr`'s remainder has width `|p|`. True for `p > 0` without coprimality. |
| `elGamal_correct` :662 | b | b | `h = g² mod p` is a unit even when `h = 1`, so `h^{ab}m(h^{ab})⁻¹ = m`. `m = 1` (the `egCanon` fallback) is covered, and `n ≥ n₀` forces `2^n > p ≥ 5`. |
| `polyTimeComputable_egGroupGenRaw` :746 | a | a | As `egGenRaw`, plus one test and a constant. |
| `elGamal_secure` :885 | b | b | Re-derived: hybrid-1 gap `η = δ + 9·2⁻ⁿ` (`1/q ≤ 8·2⁻ⁿ` for full-length p and n ≥ 2, plus `2⁻ⁿ` for `egUnit`). Total `2η + ε₀ + ε₁ + 2·2⁻ⁿ`. DDH is assumed for the derived generator (declared). `hbig` is avoidable (M1). |
| `Concrete` `statClose_rejectBlocksL` :554 | a | a | True for all parameters, including `T = 0` (bound 1) and `k = 0`. |

**Pack question: does any statement need a field the bundle lacks? No.**
- The candidate that looks like one is the binary numeral of `n^c` in `fullDLCollection_hardCore`'s machine (§1.3 item 4).
- It is a fill-level need, met by advice. It is not a statement need.

---

## Missed by the auditor

### M1 (minor, docstring; optional statement strengthening): `hbig` is dispensable in both headline theorems, but the docstrings call it "needed"

**The claims in the docstrings:**
- `DiscreteLog.lean:51–52`: "the prime must have full length `2^{n−1} ≤ p`".
- `:319–321`: "Needed, with `Negligible δ`, where the proofs divide by `q` or `p − 1`".
- `ElGamal.lean:845–847`: "`hbig` … makes the sampling term `1/q ≤ 8·2^{-n}` negligible".

**Why `hbig` is avoidable:**
- **`fullDLCollection_hardCore`.**
  - Let `B₁` invert by exhaustive search when `p − 1 < 16n^c` (at most `16n^c` calls of `H.modExp` in an `iterateFind` loop; the numeral `⟦16n^c⟧` goes in the advice).
  - Let `B₂` be the window inverter of §1.4 when `p − 1 ≥ 16n^c`.
  - On the good set (probability `≥ ε`), `dlProb B₁ + dlProb B₂ ≥ ε·3/(4K(n)) − (1+16n^{2c+2})2⁻ⁿ`. So one of them is non-negligible infinitely often, contradicting `hDL`.
  - Nothing uses full length.
- **`elGamal_secure`.**
  - Suppose `E_r[1/q_r] ≥ n^{-c}` infinitely often. Then `Pr[q ≤ 2n^c] ≥ n^{-c}`, because `1/q ≤ 1/2` always.
  - The DDH distinguisher that, when `q ≤ 2n^c`, finds `a` by search from `A = h^a` and accepts iff `Z = B^a` has advantage `≥ n^{-c}/2 − 2⁻ⁿ` against `egGroupGen H G`. This contradicts `hDDH`.
  - Hence `Pr[g² ≡ 1] ≤ E[1/q] + 2⁻ⁿ` is negligible without `hbig`.
- **Why it matters:** with negligible δ, `hbig` is not known to be satisfiable without an unproved safe-prime density conjecture. `FullLengthExcept`'s own docstring calls it "itself open". It is therefore a real extra assumption, and an avoidable one.
- **Not a weakening relative to the source:** [PS10]'s `Π̃_n` has full-length p by definition. So the (b) verdicts stand.

**Fix (recommended, option A; no statement change).**
- `DiscreteLog.lean:51–52`: "the prime must have full length" → "the proofs use full length".
- `:319–321`: "Needed, with `Negligible δ`, where the proofs divide by …" → "Used, with `Negligible δ`, by the proofs that divide by … (a convenience: instances with `p − 1` below a polynomial can be inverted by exhaustive search, so `hbig` could be dropped; gate 03f1 review, M1)".
- `ElGamal.lean:845–847`: likewise.

**Optional ruling R-03f1-1, only if the stronger statements are wanted.**
- **(A) Keep `hbig`, fix the docstrings (recommended).** Cost: none now. The two theorems stay conditional on an avoidable hypothesis.
- **(B) Drop `hbig` from `fullDLCollection_hardCore` and `elGamal_secure` before the fills.**
  - Cost: two statement changes; a brute-force branch in dl-b and a small-q DDH distinguisher in dl-c (each a bounded `iterateFind` search); revision of DESIGN §5 item 21 and the P8-2 record.
  - No ch. 5–8 ripple: neither theorem is cited there.
- **(C) Defer to a post-fill strengthening.** Cost: a second statement change later, and a re-audit of the two theorems then.

**Ripple:** docstrings only under A. Under B, packs 03f1 (re-audit of two statements) and the dl-b and dl-c fill briefs.

### M2 (minor, duplication): `sampleBelowL` is `rejectBlocksL (· < m)`

**Check.**
- `sampleBelowL m k B T r` (`DiscreteLog.lean:465–468`) and `rejectBlocksL E k B T r` (`Concrete.lean:517–520`) have the same body with `E := (· < m)`. The block layout is the same, `drop (t*B)` then `take k`.
- `DiscreteLog` imports `Concrete`.
- So `statClose_sampleBelowL` is `statClose_rejectBlocksL (· < m) (Nat.size m) n n (Nat.size_le …) (d := 0)`, followed by `{v : Fin (2^k) // v < m} ≃ Fin m` and `(1 − m/2^k)^n ≤ (1/2)^n`.
- `sampleBelowL_lt` likewise follows from `rejectBlocksL_spec`.
- Both lemmas are admitted, and the fill brief draft (`fills/dl-candidates/brief-draft.md:50`) says they "differ in the block layout". Following it, dl-a would fill the same lemma twice.
- `Concrete.lean:516` already notes that `sampleBelowL` "has the same shape", so this is a disclosed similarity. It is not yet a dedup.

**Fix.**
- Add `theorem sampleBelowL_eq_rejectBlocksL : sampleBelowL m k B T = rejectBlocksL (· < m) k B T := rfl`. This is a new lemma; no definition changes, so prong A's `expSampleRaw` and `DLHash` are untouched.
- Re-point `statClose_sampleBelowL`'s sketch (`:487–498`) to it plus `statClose_rejectBlocksL`.
- Fix the fill brief: dl-a fills `statClose_rejectBlocksL` first.
- Optionally add a duplication-ledger line.

**Ripple:** dl-a's order. None in ch. 5–8.

### M3 (minor, sketch staleness): "requested shared primitive(s)"

**Check.**
- `DiscreteLog.lean:517` (`polyTimeComputable_expSampleRaw`) calls `Nat.size` a "requested shared primitive". The auditor noted this one, in row 38.
- `ElGamal.lean:512–513` (`polyTimeComputable_egGenRaw`) calls "the decrement `p − 1` and the bit length `Nat.size`" "requested shared primitives". The auditor did not flag this one.
- Both are bundle fields since P7-1: `H.sub` and `H.size` (`Arithmetic.lean:252, 263`).
- The fill brief's rule "if a needed operation is missing from the bundle, report it" makes the stale words a source of spurious escalations.

**Fix.** Replace each phrase with "(`H.size`)" and "(`H.sub`, `H.size`)" respectively.

**Ripple:** none.

### M4 (note, records): ch. 5–8 uses more of this pack than the pack declares

**Check.**
- `03f1-pack.md:90–91` says the declarations cited by ch. 5–8 are `ExpGroupGen` and `DLAssumption`.
- Prong A's `Authentication/DLHash.lean` (`2d7b5441`) uses `ExpGroupGen`, `ExpGroupGen.DLHard`, `ExpValid`, `dlM`, `dlP`, `expGenFun`, `expSampleRaw`, `expEval`, `expF_injective` and `statClose_sampleBelowL`.
- `dlHash_crh` assumes full-group DL (`hV : … dlM i = dlP i − 1`, as in Lemma 84.1), not `DLAssumption`.
- None of this review's fixes changes those declarations. M2 keeps `sampleBelowL`'s definition for this reason.

**Fix.** Correct the interface list in the S1 note and the gate records, so that later repairs to these files check prong A.

**Ripple:** records only.

### Smaller corrections to the auditor's notes (no change requested)

- Row 15 (#3) and row 13 cite `ElGamal.lean:49, :294`. The text is at `:57–62` and `:295–298` (see §3).
- Row 72 (`good_instances`): the lemma's `ε/2` is weaker than what its hypotheses give (`ε/(1−ε)`). It is still correct as stated and is proved.
- Row 141 (Claim-53.2): agree. `DiscreteLog.lean:91`'s "(Claim-53.2 of the inventory, proved)" gives injectivity into strings only. Reading "permutation" as "bijection onto its image" makes it acceptable; no change needed.

---

## Proposed closing condition for gate 03f1

1. **The major's fix.** #1's corrected sketch (§1.4, with `:561`) is merged as a docstring-only change.
2. **The minors and M-items.** #3, M1 (option A), M2 (the `rfl` lemma and the sketch re-point) and M3 are merged in the same docstring PR. #2 and M4 are applied to the records.
3. **Evidence for the PR:**
   - a statement byte-identity check of every declaration in the four files against `0c348ff9`, with only docstrings changed and one new `rfl` lemma;
   - a lint run on the four files;
   - re-check of the four modules and their downstream closure (prong A not required);
   - axiom prints unchanged except for the new lemma, which must print standard.
4. **Closing round 2** (delta pack, as for 03b, 03c and 03e round 2): an external check that the new sketch is consistent (coin budget, constants, `T < 2^n`, advice numeral) and that no statement changed. The gate closes at 0 blockers and 0 majors.
5. **Fill briefs.** The dl-a and dl-b fill briefs are revised before issue:
   - the dl-a order (M2);
   - dl-b's dependency on `statClose_sampleBelowL`;
   - the advice route for `⟦8n^c⟧`.
6. **R-03f1-1** needs a user decision only if option B or C is wanted; otherwise none.
