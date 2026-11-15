# Concrete phase-wrapper instantiation of statClose_normalized_step

This is the exact reader-only instantiation recipe, not an additional public declaration
or a separately checked Lean proof. The generic theorem has no dependency on WrappedVerifier.

Fix the original protocol pi, efficient cheating verifier V, instance x, witness y with
R x y, original z, fixed original verifier tape rV, phase i, and earlier prefix pre. Let

  rho = pi.withV (phaseVerifier V),
  aux = phaseAux z rV i pre,
  k = pi.rounds.eval |x|,
  p = the count from PaddedProverSpec,
  b = B.eval |x|.

Choose S and hS by applying the StatZK premise, through StatZK_iff, to phaseVerifier V and
its public phaseVerifier_efficient proof. No simulator efficiency premise is passed to
statClose_normalized_step; hS supplies its raw statistical premise at this aux.

The generic call is

  statClose_normalized_step rho S x y aux pre p b (delta |x|)
    hcoins hP hcount (hS x y aux hR).

Its three structural premises are obtained only from public readers:

1. hcoins: rewrite (pi.withV W).V by Protocol.withV_V, then use
   phaseVerifier_coinLen V |x| = 0.
2. hP: introduce the raw prover tape and history, rewrite (pi.withV W).P by
   Protocol.withV_P, then apply
   (Protocol.proverBounded_iff pi R B).1 hB x y tape hist hR.
3. hcount: introduce the raw prover tape. Rewrite Protocol.withV_P, withV_V,
   withV_verifierFirst and withV_rounds in the execution expression. Then use
   hSpec.original_count (phaseVerifier V) y aux tape [].

The supplied count reader is valid for every verifier and every verifier tape, so using
[] introduces no extra premise. The generic theorem proves its real normalization fixed
point from exec_snd_bounded and the given count, rather than asking the caller to assume
that fixed point or any simulated output shape.

The result is precisely

  pre ++ real wrapped phase received messages ++ replicate(k-p)[]

versus

  pre ++ normalizePhaseMsgs x aux p b (S.simulate x aux seed) ++ replicate(k-p)[].

The real seed type is deliberately rho.P.Coins |x|. Keep that same alpha in the generic
StatisticalRecursion application to avoid a dependent withV cast at every one-phase step.
Public withV field equations rewrite the list-valued execution expressions to pi.P and
phaseVerifier V. At the final endpoint, the scalar coin-length equality

  (pi.withV W).P.coinLen |x| = pi.P.coinLen |x|

follows by rewriting Protocol.withV_P. Combine it with hSpec.prover_coinLen to build one
explicit finite coin-table equivalence for the final full tape; do not rely on implicit
definitional coercions. The final simulator coin layout is already exposed by b's
exists_phaseSimulator and phasePrefix_succ_simulate readers.

No new host, frozen edit, statement weakening, or duplicate concrete phase proof is needed.
