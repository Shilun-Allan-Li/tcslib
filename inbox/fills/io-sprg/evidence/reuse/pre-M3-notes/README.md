# Claim42 pre-freeze numeric/fidelity audit and proof route

Status: READ-ONLY, NO LEAN. No source change or new import is proposed. No
false or vacuous existing assertion was found in Claim42/Load.lean or
Claim42.lean. This is a mathematical/source/API audit, not a kernel check.
Exact source bindings are in source-binding.json. The rational-delta ruling
is respected. No M0 statement repair or additional Mathlib root is identified.

## Declaration audit

| Existing assertion | Assessment and edge cases |
|---|---|
| Internal.binomial_bound | Valid for all n and positive k, including n=0 and k>n. The positive-k hypothesis is necessary for the stated denominator argument. Nat.choose_le_pow_div already handles k>n, so no Stirling reproof or extra k<=n assumption is needed. |
| Internal.bucket_tail | Valid. Strict overload means at least t+1 distinct witnesses. [NeZero B] excludes undefined uniform Fin0 labels and makes every denominator positive. B=1, m=0, S empty, t=0, and t>=S.card are all covered. |
| Internal.some_bucket_tail | Valid union bound, explicitly multiplying by B. It may exceed1, which is harmless for an upper bound. |
| Internal.full_bucket_tail | Valid specialization S=univ; card= m. No threshold positivity needed. |
| Internal.some_full_bucket_tail | Valid full-set specialization plus finite union bound. |
| Params.errProb_nonneg | Direct ProbComp.prob_nonneg through errProb_eq. |
| Params.badSet_expect_le | Valid uniformly in pp and I: every dependency coordinate is nonzero with probability at most1/W, and each output uses at most cLoc coordinates. Exact nonzero probability is (p-1)/(Wp), even smaller. |
| Params.cond1_prob_le | Valid at Gamma=0 because the event implies badCount>=Gamma+1. W>0 and Gamma+1>0. No division by Gamma or m is needed. |
| Params.errProb_le_decomposition | Valid event implication. At kappa=0, all-repetitions Cond1 is vacuously true, so the RHS includes1 and still bounds error1. Common capacity failure is counted once. |
| Params.claim42 | Valid with an eventual threshold independent of pp. The supplied polynomial output-length bound controls B; neither positive output length nor stretch is needed. |

560 exact-rational finite sanity inequalities were also exhaustively checked
in Python for m=0..4, B=1..4, each canonical S={0,..,s-1}, and t=0..m+1, for
both fixed and some-bucket events. All passed; finite-sanity.json records this.
This sanity check is not a Lean proof or proof of the general theorem.

## Important dependence distinction

The Cond1 events need NOT be mutually independent after averaging over the
shared generator index I.1. The index can change each polynomial's dependency
set. The existing claim42 proof sketch correctly says to condition on each
fixed generator index. For that fixed index, the separate noise vectors are
independent and the same locality bound q applies to every repetition. First
obtain the q^kappa bound there, then average the bound. Do not copy the paper's
unqualified independence sentence as an unconditional factorization lemma.
This is a proof-route caution, not a defect in any current statement.

## Load proof plan: exact finite counting, no Chernoff implementation

1. binomial_bound: instantiate Nat.choose_le_pow_div k n in R. At x=k,
   Real.pow_div_factorial_le_exp gives k^k/k!<=exp(k). Use
   Real.exp_nat_mul 1 k to identify exp(k)=(exp1)^k. Because k>0, multiply the
   series bound by (n/k)^k and rearrange with div_pow/mul_pow. This gives
   n^k/k! <= (exp1*n/k)^k, including n=0. Reuse the existing bound; do not
   prove Stirling or another factorial estimate.
2. For a fixed T in S.powersetCard(t+1), show the event that every j in T maps
   to b has probability1/B^(t+1). Split the full function space using
   Equiv.piEquivPiSubtypeProd (fun j=>j in T) (fun _=>Fin B). Use
   uprob_comp_equiv and uprob_fst to discard unused coordinates, then apply
   OneWay.uprob_pi_forall on the subtype T with constant predicate (=b),
   OneWay.uprob_eq_one_div_card, and Fintype.card_coe.
3. If the bucket intersection is strictly above t, Finset.exists_subset_card_eq
   extracts a t+1-element subset of that intersection. Its subset of S belongs
   to powersetCard. Apply uprob_mono, uprob_exists_le over this finite powerset,
   the fixed-subset formula, and Finset.card_powersetCard. If t+1>S.card the
   powerset is empty and both the overflowing event and choose coefficient vanish.
4. Apply uprob_exists_le over Fin B for some_bucket_tail. Sum a constant and
   read Fintype.card_fin; the factor B must remain.
5. Specialize to S=univ for both full-load theorems, using bucket_eq/load_eq,
   Finset.inter_univ, Finset.card_univ, and Fintype.card_fin.

OneWay.uprob_pi_forall accepts a CONSTANT predicate across coordinates. The
selected-coordinate split in step2 is therefore relevant; do not assume a
stronger heterogeneous-coordinate version exists. Equiv.piEquivPiSubtypeProd
is already public Mathlib API, so no new custom choice equivalence is needed.

## Claim42 proof plan with coarse elementary bounds

Write a=m*kappa, W=P.W kappa, B=P.B kappa, c=P.cap kappa. From the existing
readers and W_pos/B_pos obtain these arithmetic glue inequalities:

- a<=B*W (the rounded-up quotient bound);
- B<=a+1 (a positive integer denominator cannot increase the rounded quotient);
- for kappa>=1, c=kappa^2*W>=max(kappa,W), hence B*c>=m*kappa;
- Gamma<=B eventually (existing Params.Gamma_le_B).

There is no need to analyze rational powers, floor growth, or delta in this
proof. W>=1 suffices. Delta/rounding asymptotics are needed elsewhere, not here.

1. Nonzero scalar noise is at most1/W uniformly in p, using the scalar noise
   readers/law plus uprob_not. For each output, union-bound over its vars.
   Sum indicators with ProbComp.expect_sum and use HasLocality_iff. This proves
   badSet_expect_le; no claim that different output errors are independent.
2. For cond1_prob_le apply the EXISTING
   LamportReduction.expect_favourable_of_success with q=real badCount and
   b=Gamma+1. A strict natural inequality implies that lower bound. Divide by
   its positive threshold and use badSet_expect_le.
3. Eventually log2(n)>=4*cLoc, by existing le_log_n. Nat.lt_mul_div_succ at
   a=m*log2(n), denominator W gives a<W*(Gamma+1). Thus
   4*cLoc*m<=W*(Gamma+1), and the Markov upper bound is at most1/4.
   This multiplication proof works even m=0 or cLoc=0; avoid dividing by m or log.
4. Conditional on each fixed generator index, OneWay.uprob_pi_forall on the
   independent per-repetition seed type gives simultaneous Cond1 at most4^-kappa.
   Drop the irrelevant Boolean seed, matrix, bucket map and secrets using the
   existing uniform product/equivalence readers before averaging.
5. For Cond2 outside Cond1, fix the noise/generator data first. BAD has size at
   most Gamma, and the bucket map is independently uniform. Load.some_bucket_tail
   and binomial_bound give B*(exp1*Gamma/(B*(kappa+1)))^(kappa+1). Gamma<=B makes
   this at most B*(exp1/(kappa+1))^(kappa+1), eventually <=B*4^-kappa.
   Use a fixed threshold kappa>=4*exp1, rounded to a natural, or exp_one_lt_d9.
6. For Cond3 use some_full_bucket_tail at threshold c, then binomial_bound at
   c+1. Its base is exp1*m/(B*(c+1)). The inequalities above make that <=exp1/kappa
   for kappa>=1, and c+1>=kappa+1. Eventually this term is also <=B*4^-kappa.
   m=0 gives a zero binomial coefficient directly; no cancellation by m.
7. The existing decomposition now gives
     errProb <= ((kappa+1)*B+1)*4^-kappa.
   B<=m*kappa+1, G.outLen_le, PolyExpr.eval_le, and n=kappa^(E*D) bound this
   prefactor by C*kappa^s eventually. Use the EXISTING
   tendsto_pow_const_div_const_pow_of_one_lt s (r=2) and multiply by C:
   eventually prefactor/2^kappa<=1. Hence the displayed bound is <=2^-kappa.

For polynomial bookkeeping, reuse PolyExpr.eval_subst/eval_add/eval_mul/eval_pow
and eval_le on one composed expression bounding ((kappa+1)*B+1), instead of
reproving generic polynomial-growth closure by structural induction.

Uniformity: the final threshold depends on P, cLoc and G.outBound's majorant,
not p or a PrimeSchedule. The bound1/W removes p before any eventual estimate.
The only dependence on the generator index is removed by a uniform locality
bound before averaging. No per-prime asymptotic threshold may be selected.

## Parameters lemmas: short routes worth preserving

- le_log_n P c: choose kappa0=2^c. From kappa>=kappa0 and le_n derive
  2^c<=n kappa; apply Nat.le_log_of_pow_le. This avoids real logarithm analysis.
- Gamma_le_B: eventual log2(n)<kappa follows from n=kappa^(E*D) and the existing
  tendsto_pow_const_div_const_pow_of_one_lt (E*D) (r=2), then
  Nat.log_lt_of_lt_pow. Compare the floor and positive rounded-up quotient.

## Import and probe status

No new import is needed for this route. A comment/string-aware static import
walk found2223 reachable TCSlib/Mathlib modules. import-audit.json lists the
relevant modules, all already reachable: Powerset, Equiv.Prod,
SpecificLimits.Normed, Pow.Asymptotics, Log.Basic/Base, Exp,
Complex.ExponentialBounds, Nat.Log and Archimedean.Basic. No
Logic.Equiv.Finset import is required (it is absent but unused).

The earlier naive import walk counted2225 because it included two textual
examples. The corrected comment/string-aware walk retains all needed APIs.
This is static import evidence, not a Lean environment declaration census.

All proposed helper names/steps still require root exact?/apply? probes before
landing helper proofs. No exact?/apply?/simp? output or kernel validation is
claimed. Existing generic APIs and exact source locations appear in APIs.tsv.
