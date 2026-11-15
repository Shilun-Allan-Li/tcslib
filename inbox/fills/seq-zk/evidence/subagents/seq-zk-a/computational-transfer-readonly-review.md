# Read-only review of the computational transfer draft

Reviewer: seq-zk-a. Draft: root evidence/drafts/ComputationalTransfer.lean,100lines.
Draft SHA256: `bbd9d2f6dc2ee0553187e6f67c3909bf3aa8561171b4f403f50fea22aba322f0`.
This is explicitly an uncompiled draft. No Lean command and no source edit was performed
for this review. Actual current b/c/a helper statements, not proposed interfaces, were
compared. Exact input paths/hashes are computational-transfer-readonly-inputs.json.

## Result

No concrete API, dependent type, quantifier, arithmetic, or mathematical mismatch found.
The lead must still integrate checked dependencies and native-check the draft. The
separately announced foreign-withV-coin transport correction in ContinuationProbability
keeps its public API unchanged and does not change the transfer arguments reviewed here.

## Binder and reader checks

| Draft line | Call | Actual signature check |
|---:|---|---|
|60|ZK_iff ρ R|Both protocol and relation are explicit; .2 expects the stated target.|
|63–64|ZK_iff π R / phaseVerifier_efficient|The ZK reader quantifies explicit verifier then efficiency. The efficiency lemma's V is implicit and is correctly supplied by `(V := V)`.|
|65–66|exists_phaseSimulator|Explicit S,hS,k,B,Q,CV,verifierFirst receive S,hS,π.rounds,B,Q,V.coins,π.verifierFirst in exactly that order.|
|69|exists_negligible_phase_bound|Explicit π,R,V,S,hS,hclose,Lz,D,Q,B match b's current theorem; final Q/B order is correct.|
|70|Negligible.mono|The expected type fixes ν n=abs(ε n). The pointwise obligation is abs(abs(ε n))≤abs(ε n), closed by abs_abs. Zero is a valid eventual-bound index.|
|71|Negligible.polyExpr_mul|ReductionSupport publishes `(hμ : Negligible μ) (p : PolyExpr)` and conclusion `(p.eval n:ℝ)*μ n`; method call `habs.polyExpr_mul Q` is exact.|
|74|Protocol.proverBounded_iff|Explicit π,R,B; pointwise arguments x,y,r,hist,hxy correctly produce the direct next-message cap.|
|85–86|PaddedProverSpec.realPrefix_bounds|Implicit π,ρ,x,q,p are determined by hspec x. Explicit V,y,z,rV,j,hj,B,hbound,coins match the supplied arguments.|
|89–90|prefix_distAdv_joint_le|Explicit S,B,Q,d,V,y,z,D,hp,hbound,ε,hε,hlocal all match c's current theorem. The implicit C resolves as D.Coins x.length.|
|96–98|distAdv_view_endpoints|Explicit d,V,y,z,S,SQ,B,hp,hlen,hsim,D match. The equality has actual advantage on its left, so trans_le with hprefix has the required orientation.|

The previous implicit-V application mistake is absent. RealPrefixBounds and both hybrid
functions take V explicitly; phaseVerifier_efficient takes it implicitly. The draft uses
those different conventions correctly. Implicit p equals the exact mover-dependent count
from hspec, so both hp arguments are reflexive equations.

## Local premise and arithmetic checks

At82, hphase receives x,y,z,ofFn rV,i,and the reached real prefix, followed by hxy,hz.
The three remaining premises, in order, are exactly the verifier-tape length, i<Q,and the
encoded-prefix bound. Thus the three bullet proofs match the theorem's binder order.
`rw [List.length_ofFn]` at83 changes the tape-length equation to reflexivity; no incorrect
explicit application of the length lemma is present.

RealPrefixBounds supplies encLength≤(i*k)*(2*B+2), for k=π.rounds.eval x.length. The inner
`Nat.mul_le_mul_right k hi.le` gives i*k≤Q*k. The outer multiplication by2*B+2 gives exactly
(i*k)*(2*B+2)≤(Q*k)*(2*B+2), with the same left association as b's requested envelope.
The .2.2 projection of the aggregate bound is the encoded-length inequality.

## Uniformity, sign, and endpoints

SQ is chosen before Lz,D at65–68, so the ZK simulator quantifier order is preserved. The
metadata reduction chooses one negligible error uniformly over all actual witnessed inputs,
auxiliary words,tapes,phases and bounded prefixes for each fixed Lz,D. The absolute error
is nonnegative at every length and remains negligible; multiplying by Q is the exact
public polynomial-closure theorem. No nonnegative premise on the original selected ε is
needed.

The hcoins witness is SQ.coins=.add V.coins(.mul Q S.coins). Expanding only published
coin/evaluation readers gives hlen exactly. The simulator endpoint expects take/drop at
V.coinLen |x|, while hsim uses V.coins.eval |x|; `Strategy.coinLen_eq` identifies them.
The let bindings for the split tape reduce locally. Both typed prefix samplers in hprefix
match the right side of distAdv_view_endpoints, so its equality transfers the bound to
the actual repeated view and SQ.simulate.

Q(|x|)=0 needs no call of hlocal; the prefix/endpoint readers compare empty histories.
k=0 likewise gives zero real and filler messages. Odd k,both first-mover flags,arbitrary
cheating-verifier filler replies,and malformed simulator outputs are handled by the
existing padded-prover and normalization contracts rather than extra draft assumptions.

## Limits

This review does not certify elaboration performance, implicit reduction under Rule10 seals,
or completion of b/c's current native checks. The nested concrete .trans_le application
is mathematically aligned; if elaboration later stalls, typed intermediate sampler/equality
values would be a diagnostic refactor, not a currently demonstrated required correction.
No target statement is weakened and no additional helper is requested by this review.
