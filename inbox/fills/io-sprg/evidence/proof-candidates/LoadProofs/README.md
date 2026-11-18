# Claim42/Load finite bounds — five untested proof bodies

The five .proof files are complete replacement bodies for the five existing
Load.lean obligations. They change no statement, hypothesis, encoding, algorithm,
import, or implementation source. No Lean/Lake/build/cache, exact?/apply?, git
mutation, or agent spawn occurred. Root will perform the required overlap probes,
elaboration, seals and final dependency/axiom verification. These candidates are
NOT_RUN; source-text reasoning and static metrics are not proof validation.

Snapshot HEAD `d286bafc4b1754e26ecae89c7f7f9c2a7cb7d7d3`; Load.lean SHA256 `ba22c179a7dcf80a80cd544b8c14ae415d006f9a769ebf00836310c39ad7ff0d`.
The expected namespace is StructuredSeed.Internal with the original binders.
Candidates avoid sum notation requiring an extra open-scoped command; Finset.sum
is explicit. Each body has one outer tactic block and no nested tactic block.

| Existing theorem | Candidate | Earlier obligations it invokes |
| --- | --- | --- |
| bucket_tail :67 | 01-bucket_tail.proof | None of the new sorried results. Only the proved bucket_eq reader and existing public APIs. |
| binomial_bound :54 | 02-binomial_bound.proof | None; existing Nat.choose and exponential-series bounds. |
| some_bucket_tail :78 | 03-some_bucket_tail.proof | bucket_tail must actually be proved first. |
| full_bucket_tail :88 | 04-full_bucket_tail.proof | bucket_tail must actually be proved first. |
| some_full_bucket_tail :98 | 05-some_full_bucket_tail.proof | some_bucket_tail, hence bucket_tail, must be proved first. |

## Bucket-tail proof and exact finite API reuse

For an overflowing bucket intersection, t<card means t+1<=card. Existing
Finset.exists_subset_card_eq chooses a T inside the intersection with card=t+1.
The two components of intersection membership show T subset S and every j in T
has phi(j)=b, using only Buckets.bucket_eq and Finset.mem_filter. Thus T belongs
to S.powersetCard(t+1) by its existing membership characterization.

Apply existing uprob_mono to this implication and uprob_exists_le to the FINITE
family S.powersetCard(t+1). This reuses the public union bound directly, rather
than copying a probability/OracleComp/finite-union proof.

For a FIXED witness set T, the local hfixed equation is the direct application of
existing coordinate APIs to this particular all-equal event:

1. Mathlib Equiv.piEquivPiSubtypeProd (fun j=>j in T) (fun _=>Fin B) splits the
   table into (T->Fin B) times its complement restriction. This is an explicit
   predicate-coordinate equivalence; no Fintype.equivFin or chosen enumeration.
2. uprob_comp_equiv relabels by that equivalence. uprob_fst discards the unused
   complement coordinates, whose function space is inhabited by the constant b.
3. OneWay.uprob_pi_forall gives the |T|-th power of the single-coordinate point
   probability; OneWay.uprob_eq_one_div_card and Fintype.card_fin give 1/B.
4. Fintype.card_coe identifies the subtype cardinal with T.card. Existing div_pow
   gives (1/B)^T.card=1/B^T.card.

This is not a reproof of a generic probability-product identity or uniform-map
contract: each such step invokes its public theorem. The local hfixed statement
only records the resulting probability of the required witness event. No new
PushesUniform predicate, restriction lemma, or sampler is defined.

HardcoreBit.pushesUniform_restrict was inspected but HardcoreBit.Basic is NOT in
Load's current import closure. It is not called and no import is requested for it.
The selected explicit equivalence route is exactly the source theorem's existing
proof sketch. Unlike the general restriction theorem, it introduces no injection
range machinery or general uniform-pushforward proof.

For T in powersetCard(t+1), substitute its exact cardinal. Every summand is then
1/B^(t+1). Existing Finset.sum_const/card_powersetCard give
choose(S.card,t+1)/B^(t+1). All arithmetic normalizes the existing identities.

## Other three bucket conclusions

some_bucket_tail applies uprob_exists_le on univ : Finset(Fin B), bounds each
summand by bucket_tail, and applies sum_const/card_univ/card_fin. It does not
rederive the union bound. The full-load versions specialize S to univ and use
Buckets.load_eq, Finset.inter_univ and the existing finite-universe cardinality.
The definitions of Buckets.bucket/load are never unfolded.

## Binomial estimate without a new Stirling lemma

Nat.choose_le_pow_div gives choose(n,k)<=n^k/k!. Existing
Real.pow_div_factorial_le_exp at x=(k:Real), exponent k gives
k^k/k! <= exp(k). Existing exp_nat_mul rewrites exp(k)=exp(1)^k.
Since k>0 and k!>0, public ordered division equivalences rearrange this into
1/k! <= (exp(1)/k)^k. Multiply by the nonnegative n^k and combine the powers.
A ring equality commutes the base to exp(1)*n/k. No factorial estimate, exponential
series comparison, or Stirling theorem is reproved; only the existing public term
bound is applied. k<=n is never assumed, matching the stated oversized-k case.

## Exact public source locations

| API | Public source and line |
| --- | --- |
| Finset.exists_subset_card_eq | Mathlib/Data/Finset/Card.lean:647 |
| Finset.mem_powersetCard / card_powersetCard | Mathlib/Data/Finset/Powerset.lean:176,186 |
| Equiv.piEquivPiSubtypeProd | Mathlib/Logic/Equiv/Prod.lean:463 |
| Fintype.card_coe | Mathlib/Data/Fintype/Card.lean:345 |
| uprob_mono / uprob_exists_le / uprob_comp_equiv / uprob_fst | Cryptography/Foundations/Probability.lean:120,137,165,175 |
| OneWay.uprob_congr / uprob_pi_forall / uprob_eq_one_div_card | Cryptography/OneWayFunctions/Basic.lean:50,118,144 |
| Buckets.bucket_eq / load_eq | StructuredSeed/Buckets.lean:56,64 |
| Nat.choose_le_pow_div | Mathlib/Data/Nat/Choose/Bounds.lean:30 |
| Real.exp_nat_mul / pow_div_factorial_le_exp | Mathlib/Analysis/Complex/Exponential.lean:225,250 |

All required existing sources are already in Load's current import closure.
import-closure.json records both the present requirements and the unavailable
HardcoreBit alternative; it does not claim a new direct Mathlib cache-root count.
There is no pending import or identified mathematical gap.

## Boundary and dependency audit

The witness exponent is t+1 throughout; t=0 is fully included. If t>=S.card,
the witness family is empty and choose(S.card,t+1)=0, so the same argument gives
the zero bound without changing statements or assuming an overflowing load exists.
For m=0, S is empty and this applies. B=1 is allowed: the point probability is 1,
and the stated choose bound remains valid. The selected explicit table product
works when T or its complement is empty. No positive cardinal for T is required
by uprob_pi_forall. NeZero B and the given b inhabit every unused coordinate space.

For binomial_bound, k>0 supplies the real denominator/power positivity. n=0 and
k>n are allowed; no division by n or assumption that the binomial is nonzero is
introduced. No delta, noise-width, asymptotic, or efficiency premise is added.

The three consequence bodies depend on earlier theorem obligations, which must be
filled before they constitute validated results. No such current sorry was used
as search evidence or as evidence of correctness. The independent bucket/binomial
bodies call only existing proved public library results and their owner readers.

Remaining mechanical risks: elaboration of the subtype-function equivalence under
change; rewriting uprob_comp_equiv/uprob_fst with the local equivalence; inference
of the witness cardinal in exists_subset_card_eq; and ordered-division argument
order/cast normalization in the binomial body. These have not been probed in Lean.
Root's exact?/apply? overlap searches remain pending. No claim of a green build,
seal pass, successful tactic suggestion, or standard-axiom proof is made here.

reuse-searches.json records ten successful exact-name source searches. The broader
preceding searches inspected public restriction/uniform and choose/exp alternatives;
absent guessed file paths were corrected without invoking a proof tool. Static
metrics and manifests count/bind the candidate text only.
