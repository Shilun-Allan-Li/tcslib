# Statistical API assessment

The lead approved exactly one new lemma, statClose_average, in Statistical.lean.
It takes hdelta : 0 <= delta explicitly and a pointwise StatClose comparison for each
shared seed, then averages both sides over that seed. Public readers uprob_prod
(Foundations/Probability.lean:153), abs_uexp_sub_le (Asymptotic/Sampling.lean:210),
statClose_iff (Sampling.lean:133) and StatClose.abs_uprob_sub_le (Sampling.lean:138)
are directly reused. No averaging argument is copied; this packages their sampler-level
consequence needed for conditional phase comparisons. A future promotion beside StatClose
in Asymptotic/Sampling.lean is requested when the shared-file window opens.

## Why the explicit nonnegative premise is necessary for the fully generic helper

The omitted-hdelta draft interface, with only finite alpha,beta,gamma, is false. Take alpha
empty, beta and gamma equal to Unit, output Unit, and delta=-1. The pointwise hypothesis
forall a, StatClose (F a) (G a) delta is vacuous. Both product seed spaces are empty, so for
every test both probabilities are zero; the desired conclusion requires |0-0|<=-1, which is
false. This is a counterexample to the draft helper API, not a flaw in a frozen target.
The issued phase-prefix coin types are nonempty. The lead can also derive delta>=0 from
a real witness's one-phase comparison using StatClose.nonneg (Sampling.lean:149).

## Randomized suffix: reuse, no new declaration

The desired randomized postprocessing is already exactly exposed by
StatClose.abs_uprob_sub_le_prod (Asymptotic/Sampling.lean:237). Given h : StatClose f g delta,
and K with an independent finite suffix seed kappa, construct the desired StatClose using

  (statClose_iff _ _ _).2 fun T =>
    h.abs_uprob_sub_le_prod (fun v k => T (K v k))

This covers empty suffix seed types as well; h itself guarantees delta>=0. Therefore no
randomized-map wrapper declaration was added. The deterministic normalization stage uses
the existing StatClose.map (Sampling.lean:174). Their proofs are reused unchanged.

statistical-searches.log contains the raw TCSlib and Mathlib searches run before writing.
