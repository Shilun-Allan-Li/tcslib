# Delivered proof route and edge cases

This describes the committed proof at `5a24269932a72f672104b18280609879dd992c82`,
relative to issue base `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`.
Source references below are repository paths and one-based lines at that head.
The statement of `Authentication.dlHash_crh` is preserved.

## Actual proof

1. **Read the honest key.** The user-authorized provider readers are
   `expGenFun_eq` and `expSampleRaw_eq`
   (`TCSlib/Cryptography/Candidates/DiscreteLog.lean:486`, `:657`).
   `dlHashIdx_layout` and `dlHashGenFun_layout` expose generator and sampler tape
   segments (`TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:91`, `:121`).
   `dlHashGenFun_key` (`:141`) proves the sampled exponent, including the fallback,
   is below the positive order and identifies the key as `⟨i, expF i z⟩`.
   The published coin equivalence and activation readers separate the two honest
   tapes (`dlHash_coinsEquiv`, `:446`; `dlHash_gen_runAt`, `:474`).

2. **Compression.** `dlHashEval_expF` (`FromDiscreteLog.lean:264`) identifies
   evaluation with the numeral of the unit `(if b then g^z else 1) * g^x`.
   `dlHashEval_range` (`:324`) proves exact output width `n` and positive value
   below `p`. `dlHash_compresses` (`:489`) uses the generator threshold, this
   range lemma, and `card_boundedInput`/`card_boundedRange`
   (`FromDiscreteLog/Encoding.lean:152`, `:164`). The cardinalities are `2m` and
   `p-1=m`, with `m>0`; hence the range is strictly smaller than the domain.

3. **Collision shape and extraction.** Equal selectors cancel their common unit
   factor. `unitCollision_selector_ne` (`FromDiscreteLog/Algebra.lean:76`) then
   applies published `expF_injective` (`Candidates/DiscreteLog.lean:299`) and
   bounded residue canonicity. For unequal selectors, `unitCollision_extract`
   (`Algebra.lean:110`) uses the generator's order and modular addition to recover
   `z.val`: the residue of `x' + (m-x)` if the first selector is true, or
   `x + (m-x')` otherwise. `dlHashEval_collision`
   (`FromDiscreteLog.lean:292`) connects distinct bit inputs and their equal
   evaluations to this unit-group statement.

4. **The concrete NUPPT reduction.** `collisionPost`
   (`FromDiscreteLog/Reduction.lean:85`) pads/truncates the finder output to two
   `(n+1)`-bit inputs, reads their exponent prefixes and the first selector, and
   evaluates the selected modular difference through subtraction, addition, and
   division. `polyTimeComputable_collisionPost` (`:116`) proves its efficiency.
   `collisionReduction` (`:287`) wraps the raw finder/output composition using
   `NUPPT.ofPolyTime`; its coin, advice, and activation readers (`:298`, `:303`,
   `:308`, `:314`, `:325`) retain the finder's tapes and advice.
   `collisionPost_split` (`:222`) covers arbitrary raw finder outputs.
   `dlHash_reduction_success` (`FromDiscreteLog.lean:579`) removes padding from
   the proved exact-length hash values, applies extraction, and proves that the
   reduction writes and decodes the canonical `n`-bit numeral of `z.val`.
   `dlHash_ideal_collision_le` (`:629`) transports equal-length finder/reduction
   coins and lifts that pointwise implication to uniform probabilities.

5. **Distribution switch and negligibility.** `collision_accept_eq`
   (`FromDiscreteLog/Probability.lean:50`) reads the CRH game as a generator-coin
   average of finder-coin probabilities. The specialized reader
   `dlHash_collision_accept_eq` (`FromDiscreteLog.lean:548`) separates the honest
   sampler tape as well. `sampleBelowL_uprob_le`
   (`FromDiscreteLog/Sampling.lean:81`) applies the published sampler closeness
   with independent auxiliary finder coins and relabels the ideal seed through
   Mathlib's value-preserving finite-residue equivalence. The canonical evaluator
   reader at `Sampling.lean:66` identifies the resulting ideal key with `expF i z`.
   Averaging and the reduction bound give `dlHash_collision_bound`
   (`FromDiscreteLog.lean:656`): for `n ≥ G.n₀`, collision acceptance is at most
   `G.dlProb B n + (1/2)^n`. The target proof (`:708`) combines `hDL B`,
   `negligible_two_pow_neg`, addition, and eventual domination. It chooses the
   collision probability itself as the all-parameter negligible upper bound.

## All six brief edge cases

| Edge case | How the delivered proof covers it |
|---|---|
| Parameters below `G.n₀` | Compression is explicitly eventual (`dlHash_compresses`, main file `:489`). Security uses `Negligible.mono` with threshold `G.n₀` in `dlHash_crh` (`:708`), so it imposes no invalid asymptotic bound below the threshold. The chosen bound equals actual collision acceptance at every parameter. |
| Invalid indices | Pointwise algebra/evaluation/reduction lemmas explicitly require `ExpValid`. The generated-index proof obtains it from `G.valid` and `hV` above the threshold (`dlHashGenFun_key`, `:141`; `dlHash_collision_bound`, `:656`). It makes no security or range claim for arbitrary invalid externally supplied indices. |
| Equal selectors `b=b'` | `unitCollision_selector_ne` (`Algebra.lean:76`) cancels the common factor and applies `expF_injective`; bounded equal exponents and equal selectors contradict input distinctness. |
| Equal exponent prefixes `x=x'` | Unequal selectors are still permitted. `unitCollision_extract` (`Algebra.lean:110`) has no exponent-inequality assumption; its modular-difference formula gives `m mod m=0` in this case. The reduction therefore recovers the zero challenge rather than discarding this collision. |
| Inputs outside `D_i` | `dlHashCollision_iff` (`FromDiscreteLog.lean:532`) retains both exponent-below-`m` guards. `dlHash_collision_accept_eq` (`:548`) proves this is exactly the CRH game's guarded event. `dlHash_reduction_success` (`:579`) consumes those guards; no unguarded finder output is counted as a successful collision. |
| Honest `y=g^w` with `w=0` | `dlHashGenFun_key` (`:141`) handles both an accepted zero and the sampler's fallback zero. The unit formula and extraction theorems quantify over every residue `z`, with no nonzero hypothesis. Thus the identity key and collisions with equal exponent prefixes are included in the same proof. |

No new hardness assumption, full-length-prime assumption, or narrowed adversary
class is introduced. The full-group equation `m=p-1` is used for compression;
the collision reduction itself only needs the valid exponentiation-group data.
