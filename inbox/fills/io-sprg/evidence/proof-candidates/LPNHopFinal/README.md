# M4 LPN hop: full intended candidate chain — NOT RUN

Recommended existing body:10-lpn_hop.proof. Theorem-only supporting candidates01-09
are intended for the area-local StructuredSeed.Internal namespace before lpn_hop.
No existing statement, algorithm, sampler, encoding or assumption changes.

NO Lean/lake/build/cache, source edit, git mutation, new import, machine/sampler
construction or agent spawn occurred. Every body is untested. No exact?/apply?,
compilation, tactic, seal or kernel success is claimed. Canonical casts and typed
Fubini rewrites are explicit root pretest points below. Do not interpret an
unverified final simp/rfl as evidence that a transport goal is closed.

## Dependency and root pretest order

| File | Exact role |
|---|---|
|01 lpn_accept_realizes_eq|shared layout-only verdict + actual B coin equivalence + short uniform prefix, no legacy coin lemma|
|02 lpn_gap_realizes_eq|canonical raw LPN advantage equals the fixed ideal short-coin gap for EVERY realiser|
|03 lpn_uniform_challenge_reindex|explicit uniform canonical matrix/value equivalence with projection equations|
|04 lpn_real_seed_reindex|coherent canonical real seed equivalence AND matrix/noisy-value equations; narrow hardest cast pretest|
|05 lpn_pre_real_update|pointwise actual preprocessing word equals chain word after updating selected secret/noise repetition|
|06 lpn_pre_uniform_update|pointwise word equals next chain after updating selected public vector by b+sigma|
|07 lpn_real_section|fixed-advice canonical real acceptance, using04/05 and existing acceptProb_comp_equiv|
|08 lpn_uniform_section|fixed-advice canonical uniform acceptance, using03/06 and existing conditional translation law|
|09 lpn_fix_advice|ACTUAL finite nuisance law, two complete section-average attempts, convexity and finite maximum; NO B parameter|
|10 lpn_hop.proof|choose one global advice family before B, then shared realiser equality, reindex by current kappaOf_pow|

The CURRENT source name is Params.kappaOf_pow: P.kappaOf(P.ell kappa)=kappa.
The old packet's kappaOf_ell spelling is stale; no alias or source rename is proposed.

First compile01/02 and03. For04, test hQ/hchi/type equality separately, then the
last TWO coordinate simp goals (matrix and noisy value). Those are the exact
remaining narrow goals if simplification does not close them; retain the goals
and reuse cast/finite-sum APIs rather than assuming a type equivalence preserves
sampling. Next test05/06 pointwise word equalities,07/08 canonical sections,
then09.hreal/huniform and10. No helper invokes the target lpn_hop or its sorry.

## Actual nuisance law and advice quantifier order

09 uses the finite nonempty type
  Omega = G.IdDraw(n) x buckets x sigma x repetitions x allPublicUniforms x tail.
All factors follow their ACTUAL laws: G indices are G.idCore of uniform G.IdDraw,
not uniform over G.Idx. The full source Draw is split into its Boolean seed and
full repetition table via existing product expectation APIs. Uniform public
vectors and the comparison tail are retained, including coordinates later
unused by the preprocessor. The challenged matrix is NOT an advice field.

The proof-local mk nuisance tuple produces the existing LPNAdvice record:
fixed hop, actual mapped G index, actual buckets, complete sigma/repetition draw,
all public uniforms, and tail=G.eval(I,sigma) if tailReal else the sampled tail.
This is proof-only hardwiring, not a new honest algorithm/encoder/preprocessor.
It is legitimate for the selected tail to correlate with I and sigma.

Each fixed tuple has ideal real/uniform canonical acceptance R(nu),U(nu), using
A's SHORT typed coins. Section identities identify the adjacent chain acceptances
as the SAME nuisance expectation of R/U. Existing abs_expect_sub_le_expect bounds
the absolute difference of averages by the average of absolute differences.
Existing LamportReduction.exists_expect_sample_le selects nu whose absolute gap
is at least that average. There is no factor2, orientation bit or uniform-advice
assumption.

Crucially09 has NO B argument.10 chooses the entire family omega(L) from this
ideal gap before introducing B or its RealizesOn hypothesis. On-image valid hops
use09; off-image/sentinel cases use the existing Nonempty advice type in proof.
At L=ell(kappa), current kappaOf_pow recovers the same kappa, tails and hop.
This ensures a single family works for all kappa. At kappa=0, Fin(kappa+1)
remains inhabited and the requested hop.val<kappa premise is impossible.

## Concrete real/uniform sample compatibility

03 composes lpnChalEquiv with PUBLIC arrow/product equivalences and finCongr to
obtain the actual (Mat_kappa,Vec_kappa) coordinates. Its projection equations
are proved through lpnMatrixAt_eq/lpnValuesAt_eq, not a chosen enumeration.
Uniform canonical input may consequently be reindexed by acceptProb_comp_equiv.

04 reads canonical dimensions, sample count and modulus through the published
lpn_dimension_eq/lpn_samples_eq/lpn_modulus_eq. It also reads the actual scalar
noise through toLWE_noise/noise_eq and raw family modulus/noiseDen readers,
using L=ell(kappa) and W_eq_noiseDenAt. The type isomorphism is an Equiv.cast
on the derived seed-type equality, not Classical.choose.

Its RESULT ALSO REQUIRES pointwise sample coherence, explicitly:
  lpnMatrixAt(sample Q chi r)=(e r).matrix;
  lpnValuesAt(sample Q chi r)(i)
    =sum_a matrix(i,a)*secret(a)+noiseValue(noiseSeed(i)).
The final two simp blocks attempt those equations using existing sample_fst,
sample_snd,noisyValues_apply, noiseValue_eq and cast-transitivity APIs. They
are the highest-risk untested blocks. If they leave a goal, it is a narrow
finite-cast/sum/noise-core identity, not permission to replace the actual
canonical experiment. No law preservation is inferred from the type equality.

05/06 then prove exact preprocessing-word equalities by reading lpnPre_eq,
chainPublic_eq and lpnVector_eq and splitting the finite order tests. Fresh
secret/noise updates ONLY the selected repetition; every later real vector uses
the SAME challenged matrix. The uniform word includes b+sigma exactly once.
No G.eval or sampling is added inside lpnPre.

## Actual-law averaging, with existing resampling APIs

07 reindexes canonical real seeds using04 and acceptProb_comp_equiv, then05
identifies the word. It yields fixed-advice acceptance over Mat, freshRep,
and A's typed short coins.08 uses03/06 for Mat,uniformVec,coins. For its fixed
sigma, HardcoreBit.pushesUniform_add_right + pushesUniform_iff removes the
translation b+sigma from the uniform average. This remains valid when the
tail is correlated with sigma; sigma is fixed before this law is applied.

09.hreal expands the actual nuisance PRODUCT using the EXISTING
Games.Bridge.expect_sample_pair plus expect_bind/expect_pure. It uses typed
expect_sample_comm rewrites to move the challenge Mat past Tail,U,Table,sigma,
then freshRep past Tail,U. The resulting Table/freshRep block is exactly the
EXISTING expect_sample_update at the selected coordinate. It recovers the
original Table law, preserving sigma and hence the hardwired correlated tail.

09.huniform moves Mat in the same four steps, then uniformVec past Tail.
The U/uniformVec block is again expect_sample_update, now for the public-vector
table. It recovers the original U law of the NEXT chain. This includes its
ignored old selected vector, without asserting free-OracleComp equality.
Both sides then normalize to the exact chainGame expectation using its reader,
idSamp'/idCore readers, and public NUPPT verdict/activation equations.

These are explicit typed rewrite attempts, not new Fubini, independence,
coordinate-resampling or finite-averaging theorems. expect_sample_coord was
also found, but update fits directly and avoids an extra ignored-coordinate
side condition. All comparisons are acceptances/expectations, never syntactic
equalities that erase unused oracle queries.

## Shared realiser verdict and coin layout, all independent dimensions L

01 works for every L and every canonical challenge map X. It reads B's behavior
ONLY at encoded lpnEnc challenges and at typed/layout-length coins through
RealizesOn.distinguisherL_eq, coins_eq and coinsEquivPoly_symm_ofFn. It does not
unfold RealizesOn or constrain B off the encoded language/off its coin layout.

The short/long inequality uses kappaOf_le, A.coinLen_eq and PolyExpr.eval_mono,
eval_subst/eval_var. Restriction along Fin.castLE is uniform by the existing
HardcoreBit.pushesUniform_restrict.uprob_eq. OneWay.ofFn_castLE_eq_take identifies
this exact restriction with the lpnRed prefix.02 reads canonical advantage
readers and lpnEnc_eq and applies01 to real sample/id experiments. Thus the
fixed ideal gap equals EVERY realiser's actual raw LPN advantage.

The canonical input encoder remains the family's OWN L+1-bit encoder; no kappa+1
surrogate is used in the assumption experiment. lpnPre may reencode its sPRG
challenge at kappa+1 bits as already defined. No challenge/law/assumption changes.

## Reuse, imports, source size and verification boundary

Searches covered sampler-law/encoding/coincast compatibility, experiment
reindexing, finite averaging, update-coordinate laws, uniform translation and
shared RealizesOn verdicts. Generic public APIs listed in APIs.tsv are consumed
directly. Existing legacy acceptProb_coins_equiv was found but NOT adopted;
root preferred underlying allowed uprob_comp_equiv in the specialized shared
RealizesOn transport. No forbidden direct import or legacy helper dependency is
introduced. Every needed module is already in the current static import closure.

All proposed helpers need root exact?/apply? searches and actual Lean checks
before landing. The candidates have full intended closing steps and no
intentional sorry/admit, but this is not a claim that the simplifier/rewriters
close every cast or section-normalization goal. In particular04 and09 need small
pretests before attempting the whole chain. Never fill failures by changing the
frozen theorem, choosing advice after B, averaging uniformly over advice, or
claiming noisyValues compatibility from a bare equivalence.

LINE BUDGET: the separate review fragments plus current428-line owner total
about999 lines before namespace wrappers/final docstrings. Do NOT append them
verbatim past the1000-line limit. Inline03's explicit uniform equivalence into08
as a local have, and/or05/06 as local pointwise haves in07/08 to remove repeated
long public headers and keep the source below the limit. These are theorem-only
proof reorganizations; no new import/module is proposed. Keep each invocation
within the one-tactic-block rule. Static metadata/hashes are textual only.
