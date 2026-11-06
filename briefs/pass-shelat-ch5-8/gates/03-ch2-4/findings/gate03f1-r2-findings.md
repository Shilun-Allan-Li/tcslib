# Gate 03f1, round 2 — delta audit findings

**Verdict: the closing threshold is met — 0 blockers, 0 majors, 1 minor.** The rewritten `fullDLCollection_hardCore` sketch repairs round 1's major. Its coin budget, ceiling bound, statistical loss and final success constant are correct. A worker can follow this route to prove the unchanged statement with `hbig` retained, after filling its admitted prerequisites and implementing the stated machine construction. This is a statement/sketch audit, not a completed Lean proof or an independent Lean replay. The Claim-62.2 records repair remains incomplete.

Audited the four candidate files at [commit `1ea782b11617e15a51c3e2f6bd15dd0e3befbd95`](https://github.com/Shilun-Allan-Li/tcslib/commit/1ea782b11617e15a51c3e2f6bd15dd0e3befbd95), the supplied records, and the attached Pass–shelat third edition, especially book pp.52, 58, 62, 84–86 and 105–107 (PDF pages are 12 greater). Read the first-section round-2 brief as controlling; earlier packs and reviews were evidence/context. Line numbers below refer to individual extracted files. Candidate paths abbreviate `TCSlib/Cryptography/Candidates/`.

Input fingerprints: bundle SHA-256 `e5293af00238c6d8c559e105d1e8061ee49b2b43cd5bad5ee02cfa6b0f047cf1` (20 sections); PDF SHA-256 `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`. The bundled round-1 findings reproduce the recorded SHA-256 `72909f86e53f745a24af86d23704e1eba2929189f6ab9497a67c504065203b4b`.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R2-1 | minor | `briefs/pass-shelat/inventory-ch2.md:445` · Claim-62.2; `resolutions-03f1-r1.md:9` · #2 | The inventory-location repair is only partial, despite being marked fixed. | Lines 194 and 517 now identify `Rabin.lean · rabin_symmetry`, but the detailed Claim-62.2 entry at line 445 still says “New concrete lemma in `Candidates/Concrete.lean`.” This is precisely one of the three stale occurrences identified in round 1 and in the maintainer review. | Change that sentence to “In `Candidates/Rabin.lean` (`rabin_symmetry`), audited at gate 03f2.” Retain the corrected table/checklist entries. Mark #2 fully fixed only after this remaining edit. |
| R2-2 | note | `DiscreteLogHardcore.lean:548` · `fullDLCollection_hardCore` sketch | Round 1's major is fixed; the theorem remains provable as stated. | The derivation below verifies `T ≤ 16n^c`, a fixed polynomial coin count, loss `(1 + 16n^(2c+2))·2^(-n)`, and success at least `3/(256n^(2c))` minus that loss. The predictor now receives the encoded group element rather than the ill-typed `encD y`. The advice supplies the missing binary numeral without adding an arithmetic hypothesis. | None. Complete the prerequisite admissions and machine realization during the fill; this audit does not certify their completion. |
| R2-3 | note | `DiscreteLog.lean:476` · `sampleBelowL_eq_rejectBlocksL`; `Concrete.lean:525` · `rejectBlocksL_eq`; `DiscreteLog.lean:499` · sampler sketch | Both additions are valid equations, with no implicit distributional or independence assertion. The revised corollary route is correct. | Both sides inspect `(r.drop (t*B)).take k` in increasing `t < T` and return the first accepted value. The identities hold even for empty/truncated tapes, overlapping blocks, zero trials and zero bounds. The probability corollary separately requires `0 < m < 2^n` and a full `n²`-bit uniform tape. | None. Keep the fill order `statClose_rejectBlocksL` before `statClose_sampleBelowL`. |
| R2-4 | note | `ElGamal.lean:57,296` · P8-1 history (#3) | The repaired history removes the universal claim that randomizing a generator makes DDH false. | The old coin weights are proportional to `q_r²` and `q_r³`. The displayed two-order example gives `(4/13,9/13)` and `(8/35,27/35)`, a threshold gap `36/455`. With constant order, both laws are the uniform generator-coin law, even when the generator element varies. Thus possible unrelated instance leakage, rather than universal impossibility, is the correct conclusion. The product-seed definitions are unchanged. | None required for the reported repair. Read the historical comparison as a possible difference of laws, not as an assertion that every pair of such laws is unequal. |
| R2-5 | note | `DiscreteLog.lean:51,318,525`; `ElGamal.lean:510,844` · M1 and M3 | The changed docstrings correctly describe full length as a convenience and name the available arithmetic fields. | Polynomially small DL orders can be exhausted; a non-negligible average `1/q` yields a polynomial-order DDH distinguisher. Details below. Both theorem signatures retain `hbig`, as ruling (A) requires. The two stale primitive requests have become `H.size` and `H.sub, H.size`. | None. This does not strengthen either formal theorem. |
| R2-6 | note | Four candidate files · delta completeness; `statements.txt` | No existing Lean code changed in this gate; exactly the two advertised equations were added. | Independently fetched all four files at both the round-1 pin `0c348ff94cacf24d96d99078c9dd9e328530c8d2` and the round-2 pin. Round-2 files match the bundled bytes. After removing comments and the two added declarations, all previous Lean code is identical modulo whitespace. Blob hashes agree with the repair diff. The batch manifest's other eight additions and two changed declarations are outside this gate. | None. This comparison covers definitions and proof bodies as well as signatures, without reviewing tactic proofs. |
| R2-7 | note | `evidence-repairs/03-batch/{replay,base-sync,axioms,seal,lint,maintainer-recheck}.log` | The supplied execution evidence supports the limited repair; it is maintainer evidence, not this auditor's execution. | Replay contains 129 distinct checks, all with zero return code and zero errors. The four candidate sorry counts are unchanged at 1, 6, 7, 7; all 74 modules common to base-sync and replay retain their counts. The eight-module recheck passes. The two new equations print respectively no axioms and `Quot.sound`; the sealed sampler-equation check passes and its direct-unfolding control fails. Lint reports no new warning/failure. | None affecting this gate. The axiom summary's “548 names” is a counting discrepancy: the raw output has 549 distinct names, including both `uprob_permGraph_eq_of_isomorphic` and its primed version, each standard. Correct that metadata when next refreshing the batch evidence. |
| R2-8 | note | `resolutions-03f1-r1.md:12,14` · M2/M4 records | The sampler dependency is explicit in the changed source; the additional DLHash consumers are recorded. | M2's corollary order is stated at `DiscreteLog.lean:499`. No DL fill brief is supplied, so its separate update is not independently certified here. M4's consumer list is present in the resolution. The old pack's shorter interface list remains historical context, and the delta changes none of those consumed declarations. | Before issuing fills, ensure the actual brief follows the verified corollary order and uses the corrected headline sketch. Do not treat “recorded” as an audit of the external consumer or an issued worker brief. |

**Recalculation of the headline sketch.** All bounds below concern sufficiently large positive `n` in the infinite set witnessing a predictor's non-negligible advantage. In particular, take `n ≥ G.n₀`, `δ(n) ≤ ε/2`, `2^(n−1)−1 ≥ 16n^c`, and `16n^c < 2^n`. These eventual requirements are compatible because `c` is fixed and `δ` is negligible.

1. **Good-instance mass and window.** Put

   $$\varepsilon=\frac1{2n^c},\qquad
   s=\left\lfloor\frac{p-1}{8n^c}\right\rfloor,\qquad
   T=\left\lceil\frac{p-1}{s}\right\rceil,\qquad
   k=n,\qquad \ell=16n^{2c+1},\qquad K(n)=16n^c.$$

   The assumed average prediction probability is at least `1/2 + 2ε`. Applying `good_instances` with advantage `2ε` gives mass at least `ε` with conditional success at least `1/2 + ε`. Removing short-prime coins leaves mass at least

   $$\varepsilon-\delta(n)\ge\varepsilon/2.$$

   On each remaining index, `(p−1)/(8n^c) ≥ 2`; hence

   $$s\ge\frac{p-1}{8n^c}-1\ge\frac{p-1}{16n^c}\ge1,
   \qquad 4s\le\frac{p-1}{2n^c}=\varepsilon(p-1).$$

   Consequently

   $$p-1\le Ts,\qquad
   T=\left\lceil\frac{p-1}{s}\right\rceil\le16n^c=K(n)<2^n,
   \qquad s\le p-1<2^n.$$

   The ceiling introduces no extra `+1`: `16n^c` is an integer upper bound on `(p−1)/s`.

2. **Ideal success and actual tape.** The concrete inverter's failure term is

   $$\frac{k}{\varepsilon^2\ell}
   =\frac{n}{(1/(4n^{2c}))\,16n^{2c+1}}=\frac14.$$

   Its ideal success is therefore at least `3/(4T) ≥ 3/(4K(n))`. The actual coin count is

   $$n^2+n\ell\bigl(n^2+A.\mathrm{coinLen}(n)\bigr)
   =n^2+16n^{2c+4}+16n^{2c+2}A.\mathrm{coinLen}(n).$$

   This is a fixed polynomial in `n`, independent of the index-dependent value of `T`. It gives one full `n²`-bit sampler tape for `t`, and one full `n²`-bit sampler tape plus fresh predictor coins for each of the `nℓ` trials. The advice adds only the `n`-bit numeral of `8n^c` and pairing overhead. That numeral is exact eventually because `8n^c < 2^n`.

   The loops have fixed polynomial lengths; the machine never iterates `T` times. Its stated guard handles zero window size and an oversized `T`. On malformed inputs, arithmetic and list operations remain total; correctness and the statistical estimate are used only at valid good indices. Finite exceptional parameters may return `0^n`. None of this requires deciding primality or exact group order inside the machine.

3. **Sampling and averaging.** For either sampler bound `m = T` or `m = p−1`, validity gives `0 < m < 2^n`. With sampling width `Nat.size m`, each trial accepts with probability at least `1/2`. Writing `λ` for the probability that all `n` trials reject,

   $$\lambda=\left(1-\frac{m}{2^{\operatorname{Nat.size}m}}\right)^n\le2^{-n}.$$

   Conditional on some acceptance, the first accepted value is uniform below `m`. With fallback zero, the exact statistical distance is `λ(1−1/m) ≤ 2^(−n)`. Independence of the disjoint tapes, followed by deterministic processing of all sampled coordinates, bounds the change of any success probability by

   $$(1+n\ell)2^{-n}=(1+16n^{2c+2})2^{-n}.$$

   This loss is valid regardless of the adaptive choices made during the inversion loop. Averaging on the good set and using nonnegativity elsewhere gives

   $$\begin{aligned}
   G.\mathrm{dlProb}(B,n)
   &\ge\frac{\varepsilon}{2}\frac{3}{4K(n)}-(1+16n^{2c+2})2^{-n}\\
   &=\frac{3}{256n^{2c}}-(1+16n^{2c+2})2^{-n}.
   \end{aligned}$$

   Eventually the subtracted term is at most `3/(512n^(2c))`, so the success is at least `3/(512n^(2c))` on infinitely many `n`, contradicting `hDL B`. The `δ` loss was already paid when reducing the good-set mass; it must not be subtracted again. The restriction `p ≡ 3 mod 4`, ideal challenge-exponent law, and other declared deviations from [PS10] are unchanged.

**Checks of the additional docstring claims.** Without `hbig`, the good set can be split at `p−1 = 16n^c`: exhaustive search handles the smaller orders and the same window inverter handles the larger orders. Their summed success is non-negligible, so they cannot both satisfy DL hardness. For ElGamal, if `E[1/q] ≥ n^(−c)` infinitely often and `α = Pr[q ≤ 2n^c]`, then

$$n^{-c}\le E[1/q]\le\alpha/2+1/(2n^c),\qquad \alpha\ge n^{-c}.$$

On those small orders, exhaustive discrete logarithm gives ideal DDH advantage at least `α/2`. Replacing the two real-world and three random-world exponents by their bounded rejection samples loses at most `5·2^(−n)`. The derived generator preserves `q`, so the same average applies. Thus DDH forces `E[1/q]` negligible; the square-generator error is bounded by `E[1/q]+2^(−n)`. These arguments justify the convenience wording, while ruling (A) leaves both formal statements unchanged.

**Adversarial and finite checks.** Revisited round 1's `p=523`, `n=10`, `m=522` instance. On a 20-bit all-one tape, both new-equation sides reject twice, read the next empty prefix as zero, and return zero; the equations correctly make no closeness claim for that tape. With the repaired 100-bit tape, the exact distance is

$$\left(\frac{502}{1024}\right)^{10}\frac{521}{522}
\approx0.000800211568<2^{-10},$$

whereas the old short-tape distance was approximately `0.239869341`. For `c=1`, the same valid parameter instance gives `s=6`, `T=87 ≤ 160`, `ℓ=16000`, and coin count `16,000,100 + 160,000·A.coinLen(10)`. The coarse final lower bound need not be positive at this small parameter; only eventual positivity is claimed.

Exhaustive finite evaluation checked all 26 pairs `1 ≤ n ≤ 4`, `0 < m < 2^n` against the exact sampler-distance formula; 20,160 equation cases including `m=0`, `k>B`, `B=0`, `T=0` and truncated tapes; and 24,400 floor/ceiling parameter cases. All passed. These are checks of finite semantics and arithmetic, not substitutes for Lean proofs. As a separate adversarial test of #3, a generator choosing between the two order-three generators modulo seven has the same instance-coin marginal in both old dependent-sum experiments: constant order cancels the fibre weights.

**Resolution rows.**

#1: fixed — the corrected construction, constants and advice route support the unchanged headline theorem; see the derivation above.

#2: not resolved — partially repaired, but `inventory-ch2.md:445` still gives the old location; R2-1 remains minor.

#3: fixed — the universal DDH-impossibility claim was removed, the example's weights are correct, and product seeds are preserved.

M1: fixed — the docstrings describe the optional hypothesis accurately, and both signatures retain `hbig` under ruling (A).

M2: fixed — both equations and the corollary sketch are correct; the separate fill-brief update is not present in the supplied evidence and is not certified here.

M3: fixed — both stale primitive requests now name the corresponding arithmetic fields.

M4: recorded — the additional DLHash consumers are listed in the resolution; their cited interface is unchanged by this repair.

Notes: recorded — no change requested; the unchanged 21 admissions are not reclassified by this delta audit.

**Notation.** `n` is the security parameter; `c` is the fixed natural exponent witnessing non-negligible advantage; `p` is the prime modulus; `q` is the ElGamal subgroup order; `r` denotes generator coins or, in the sampler equations, the coin list. `A` is the predictor and `B` the constructed inverter; `A.coinLen(n)` is its predictor coin count. `δ` bounds short-prime probability. `ε`, `s`, `T`, `k`, `ℓ` and `K(n)` are the displayed advantage, window size, shift count, inversion-round count, trials per round and shift-count bound. In the general sampler equations, `m` is the target bound and `k,B,T` mean sampling width, block stride and trial count; this local `B` is unrelated to the inverter. `t` is a trial or shift index. `λ` is all-trials-reject probability, `α` is small-order probability, `Pr` is probability and `E` is expectation under the specified uniform coins. A primed declaration name denotes the distinct Lean declaration carrying that trailing apostrophe.
