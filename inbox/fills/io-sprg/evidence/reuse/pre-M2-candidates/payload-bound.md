# All-parameter natural payload estimate

Goal: the existing `Params.seedBitsAt_le`, with no added hypothesis.
A sufficient concrete constant is `C = 2*(2^P.D)+12`, equivalently
`2^(P.D+1)+12`. The following derivation is in Nat throughout; division means Nat
floor division. It is not a checked Lean proof body.

Write k=kappa, e=ell(k), n=e^D, w=w(k), q=m(k)/w, K=k+1, X=n+q+1, a=2^D.
Then K>=1 and X>=1. Read only the named owner equations for lengths/parameters.

1. Reuse `add_pow_le` with e and 1:
   (e+1)^D <= 2^(D-1)*(e^D+1) <= a*(n+1) <= a*X.
   This is precisely the staged tensor candidate plus monotonicity, valid even
   at e=0. Its generic power estimate is already public and must not be reproved.
2. Prove the existing Encoding.W_le_ell_add_one before consuming it. Since
   w<=w^2=W (Core Nat.le_pow at exponent 2), and e<=e^D=n (Core Nat.le_pow using
   Params.D_pos), obtain w<=n+1<=X. This requires no new asymptotic/floor root.
3. The staged rounded-bucket product candidate gives
   B*w <= k*(q+1)+w <= K*X+X <= 2*K*X.
   Its exact generic Nat steps are listed below. This cancellation is essential:
   the coarse syntactic bound B<=m*k+1 alone loses the inverse-w saving.
4. Read sLen, rc=k*w and t=k. Its factor arrays have
   B*(rc*t+t*rc) = 2*k^2*(B*w) <= 4*K^3*X.
   Its tensor term is <=a*X<=a*K^3*X, hence
   sLen <= (a+4)*K^3*X.
5. The public+private residue count is
   k*n+1 + k*(1+2*sLen).
   The part k*n+1+k is <=K*X, since X=n+q+1. The remaining part is
   <=2*(a+4)*K^4*X. Since K<=K^4 (Core Nat.le_pow at exponent 4),
   the total is <=(2*a+9)*K^4*X <=C*K^4*X.
6. Multiply by K, read seedBitsAt_eq, and normalize powers to obtain
   seedBitsAt k <=C*K^5*X. Choose this fixed C in the existing existential.

No finite exceptional-parameter patch is needed with the global tensor bound. In
particular at k=0, e=n=0, w=1, pubLen=1 and privLen=0, so seedBitsAt=1; X>=1 and
C>=1 cover that case. If a proof chooses the simpler positive-e tensor estimate,
it must handle k=0 separately rather than assert e>=1 universally.

## Exact Nat reuse in the rounded-bucket product

Let A=m*k and W=w*w>0. The existing definition is B=max1((A+W-1)/W).
Core `Nat.div_le_div_right (Nat.sub_le _ _)` followed by
`Nat.add_div_right A hW` gives B<=A/W+1. Then

  B*w <= (A/W+1)*w
       = ((A/w)/w)*w+w
      <= A/w+w.

The equality uses W_eq, pow_two and Core Nat.div_div_eq_div_mul; the inequality
is the existing Nat.div_mul_le_self. Finally public Nat.lt_mul_div_succ gives
m<w*(m/w+1). Its non-strict version multiplied by k, followed by div monotonicity
and Nat.mul_div_left, gives A/w<=k*(q+1). This proves the proposed construction
bound without a generic new quotient theorem.

## Precise public facts

- `add_pow_le`: Mathlib/Algebra/Order/Ring/Basic.lean:130 (works for Nat).
- `Nat.pow_le_pow_right`: Core; used by the imported PolyExpr.eval_le proof.
- `Nat.le_pow`: pinned Lean Init/Data/Nat/Lemmas.lean:1239, any positive exponent.
- `Nat.div_div_eq_div_mul`: Init/Data/Nat/Div/Basic.lean:280.
- `Nat.div_mul_le_self`: same file:300.
- `Nat.add_div_right`: same file:315.
- `Nat.mul_div_left`: same file:438.
- `Nat.lt_mul_div_succ`: Init/Data/Nat/Lemmas.lean:1555.
- `Nat.div_le_div_right` / `Nat.sub_le`: existing Core monotonicity/order APIs.
- `Nat.mul_le_mul`, power monotonicity, `mul_pow`, `pow_add` and ring normalization:
  existing arithmetic API; no new induction or polynomial normalization lemma.

The proposed B*w and tensor statements are specialized glue for new Params. They
can be local named steps or disclosed helper lemmas. Do not introduce a generic
Nat arithmetic substitute for the public steps above. All uses of currently sorried
Params/Encoding bounds are explicit dependencies to fill first, not search facts
or evidence that an untested downstream proof is correct.
