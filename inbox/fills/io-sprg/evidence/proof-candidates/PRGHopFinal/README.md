# PRG and statistical hop full candidates — NOT RUN

Prepared at d286bafc4b1754e26ecae89c7f7f9c2a7cb7d7d3. Temporary proof text only:
no Lean/lake/build/cache, implementation/import/header change, git mutation, or
agent spawn. No exact?/apply?, elaboration, axiom, seal, or kernel result is claimed.
Seven new complete strings contain zero explicit placeholders, one outer tactic
block each, and lines at most91 characters. Source hashes and import/reuse evidence
are supplied. An unelaborated string is not a completed or validated Lean proof.

## Existing gaps replaced and proposed helper placement

| File | Intended owner and result | Prerequisites |
|---|---|---|
|01-sdCore_publicSeed.proposed.lean|Hybrids: Params.sdCore_publicSeed, new theorem only|publicSeed_eq; sdCore_seed/instances/err; packSeed_fst|
|02-hyb_real_prg_le.proof|Hybrids: existing statistical hop|01; actual G4_eval_sdCore; exact difference lemma|
|03-hyb_uniform_random_le.proof|Hybrids: existing statistical hop|01; exact difference lemma; no G4 correctness|
|04-prg_verdict_prob.proposed.lean|Reductions/PRG: new theorem only|shared RealizesOn verdict/coin readers; exact injected restriction|
|05-prg_nuisance_average.proposed.lean|Reductions/PRG: new theorem only|actual idCore/draw readers; explicit advice prodEquiv; pair/commute expectation laws|
|06-prg_chain_accept_average.proposed.lean|Reductions/PRG: new theorem only|05; inverse reader; explicit output-vector equivalence; preprocessor reader|
|07-prg_hop.proof|Reductions/PRG: existing every-realiser theorem|04 and06; public absolute-average and finite maximum lemmas|

Proposed helper declarations are written with Params. prefixes and assume the
area namespace outside an open Params block. To insert them before a dependent
existing theorem INSIDE namespace Params, remove only that redundant declaration
prefix. Their names/statements are otherwise unchanged. Helper01 belongs in
Hybrids, after publicSeed_eq; placing it in Correctness would create an import
cycle because publicSeed is defined in Hybrids. Helpers04-06 belong before
prg_hop. They add no definitions, algorithms, imports, global attributes, machine
or UniformSampler construction. Source implementation has not been edited.

The four already-complete historical endpoint candidates in ../PRGHop remain
referenced and hashed in inventory.tsv: hyb_real_eq_raw, hyb_random_eq_raw,
hyb_prg_accept_eq_chain_zero, hyb_uniform_accept_eq_chain_zero. Their latter two
compare ACCEPTANCE, as required by SP-W2. No free-oracle equality is asserted for
any removed or reordered unused draw. No new false statement was found.

## Actual raw-draw statistical coupling

The two statistical bodies use a common computation that samples IdDraw, Draw,
the comparison vector and A's coins, retaining their tuple. Index and full core
output are deterministic functions of that RAW tuple. Thus the pointwise
agreement proof applies only to actual core executions, never arbitrary records
of type SdCoreOut. The event is precisely core.err=true. Defining-reader and
probability laws normalize each hybrid's acceptance to its event probability;
expect_const marginalizes only the unused comparison output/coins in errProb.

The sole shared packing helper identifies the actual published seed with
publicSeed of the retained instance vectors AND the actual error bit. Off error,
that bit is false and the public vectors agree. For real/prg, G4_eval_sdCore and
eval'_eq identify the Boolean tail, including p=2 through the existing prime
instances. For uniform/random, the tail is literally the same comparison vector,
so no PRG correctness/security or G4 theorem is needed. Both then apply the
existing abs_prob_sub_le_of_agree. The generic difference bound is not reproved.

## Exact realiser and coin-prefix law

Helper04 proves the verdict probability identity for every canonical typed
challenge at every N, including off-image inputs. It reads only the shared
RealizesOn.distinguisherL_eq and .coins_eq. Reindexing uses coinsEquivPoly.symm,
whose existing list reader preserves the exact bit word. prgRed_eq exposes the
prefix. PolyExpr.eval_mono and kappaOfN_le justify the injection length. The
existing pushesUniform_restrict.uprob_eq and ofFn_castLE_eq_take prove exact
uniformity of that prefix; Bridge.prob_sample_eq_uprob moves between probability
and uniform-event notation. No longer-layout behavior outside the shared
contract, advice extraction from B, all-input realization assumption, generic
prefix reproof, alternative coin contract, or machine construction is used.

## Actual nuisance law and advice averaging

Helper05 preserves the supplied G.idSamp pushforward; G.Idx is NEVER assumed
uniform. Read idSamp'_eq/idCore_eq and G.idSamp_eq. The actual index draw splits
as G.IdDraw × (buckets × matrix); the actual seed draw splits as sigma × unused
repetitions. Advice is reindexed through its EXPLICIT PRGAdvice.prodEquiv, with
its real Fintype instance. Bridge.expect_sample_pair handles each product.
expect_const discards the unused repetitions. The remaining sample orders are:

  left:  G-index draw, buckets, matrix, sigma, uniform public vectors
  right: buckets, matrix, uniform public vectors, G-index draw, sigma.

The four explicit sample commutations in05 realize precisely that permutation.
No chosen finite enumeration, product UniformSampler, or generic product-average
identity is introduced. The generic already-published pair identity is reused.

Helper06 specializes this actual nuisance identity to the adversary's verdict.
At an image N, generalizing its inverse and substituting the image equation
reduces to N=n(kappa). kappaOfN_n activates the guard in prgPre. At chain index
kappa every k:Fin kappa satisfies k.val<kappa, so every public vector is uniform.
The explicit equivalence

  Equiv.arrowCongr (finCongr (P.m_eq kappa)) (Equiv.refl Bool)

transports the chain's m-bit comparison vector to the primitive's full output
vector, with inverse v mapped to (fun j => v (P.outputIndex kappa j)). Its sample
is reindexed exactly once under the acceptance expectation. No syntax equality
between the differing query trees is used. All conditions remain meaningful at
kappa=0 and at zero-dimensional function spaces.

Body07 chooses the entire advice family BEFORE introducing B or its RealizesOn
proof. On-image, abs_expect_sub_le_expect bounds the absolute gap by the average
section gap; LamportReduction.exists_expect_sample_le selects a section at least
that average. Off-image, the published inhabited advice default suffices for the
vacuous image implication. A proof-local sec expression abbreviates the actual
challenge experiment for analysis; it is not a new source algorithm/reduction.
Helper04 equates each fixed section to G.game B by probability, hence their
absolute gaps equal G.adv B. The final inverse identity gives the original
all-kappa theorem. No orientation bit, extra factor2, realiser-dependent advice,
new assumption, or weakened quantifier appears.

## Precise untested risks and required lead checks

All seven strings are full candidates, not checked proofs. The concrete narrow
mechanical risks are nested expectation simplifier matching; the four specified
sample permutations; normalizing the advice product equivalence's projections;
generalizing/substituting the inverse parameter in06; and dependent Eq.rec/Fin
cast normalization after the prgPre guard. The output-vector conversion is
explicitly present, not an assumed missing uniformity lemma. The shared prefix
reader has its precise layout length and direction explicitly recorded.

Root should first test04 and05 independently, then06 and07. Statistical bodies
need the M1 deterministic G4 core theorem proved; elaborating them against its
M0 sorry would not validate algebraic correctness. Run the required overlap
probes before accepting any proposed helper, excluding imported self/other M0
sorried stand-ins, followed by canonical seals. If annotations are required,
retain the existing reader/cast route instead of unfolding foreign definitions.

No known additional Mathlib root is required. import-audit.json follows current
imports, including import all syntax, and records each needed public module.
The PRG owner already reaches Bridge/HardcoreBit/OneWayLemmas/Lamport Averaging
and the shared Realization API. Hybrids' statistical bodies use only its current
Games probability/hopping and sampler/correctness imports. Closure counts are
not direct cache-root counts. The heavy BPPBridge, generic ChallengeSim import,
forbidden Games.Closeness, and CoinSampling transfer modules are unnecessary.
