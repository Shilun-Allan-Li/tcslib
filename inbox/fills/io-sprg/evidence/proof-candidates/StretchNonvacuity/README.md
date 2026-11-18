# Polynomial-stretch nonvacuity audit — NOT RUN

Source head inspected: d286bafc4b1754e26ecae89c7f7f9c2a7cb7d7d3
Binding records: dbea2807532392781304e004715f3b0190025f5e.
No source edit, Lean invocation, build, git mutation, new import or agent spawn.

## Verdict and authority

The old Raw.HasPolyStretch body only required eventual seedBits^tau <= outLen
for tau>1. Raw itself permits pubLen=privLen=outLen=0. Choose Unit index/draw
spaces, constant injective empty encodings on Unit, all lengths/bounds zero,
modulus from the supplied prime schedule, and residueBits=kappa+1. Seed/output
vectors have unique empty values; both real/random games publish identical
challenges. Advantage is zero, complexity has no output coordinate obligation,
and 0^tau<=0 holds. The bare existence conclusions can consequently be met
without the PRG or LPN assumptions. Efficiency fields in SPRG do not remove
this issue: returning empty seeds/output is efficient.

The old definition is exactly the draft in design-r1 section4.3, inherited by
r2 section4.4 and renamed to Raw by r3 sections1.1/1.4. Hence this is an inherited
design gap, not an implementation departure from those draft formulas.
Rulings contains no positive license for bounded or empty seed schedules.
Paper Def3.2 quantifies n(lambda)>=lambda, and Remarks3.1/3.2 discuss growing
polynomially expanding families. Dispatch item12 E-ROUTE explicitly includes
vacuous statements and requires a minimal disclosed repair.

Root's selected pre-M0 repair is valid:
  exists tau>1, exists kappa0, forall kappa>=kappa0,
    kappa <= S.seedBits kappa AND
    (S.seedBits kappa : Real)^tau <= S.outLen kappa.
The reader must be changed to this exact body. Primitive wrapper/reader still
reads the raw predicate. This strengthens the conclusion rather than adding
an assumption. It rules out every bounded seed family, not merely the all-zero
example; eventual positivity alone would still admit constant seed/output1.
No bare existence theorem header needs an added conjunct because the stronger
predicate now carries the growth guarantee. The construction-specific theorem41
conclusions remain about the actual final jls bundle.

## Proof impact

Actual pubLen=kappa*n+1>=1, private length>=0, residueBits=kappa+1. Therefore
seedBits>=(kappa+1) for ALL kappa, independently of pp and pi, G stretch,
locality, delta, E, hardness or targets. The candidate lower-bound body reuses
jls_seedBits_eq, Params.seedBitsAt_eq, Params.pubLen_eq, then Lean Core
Nat.le_mul_of_pos_left (Init/Data/Nat/Lemmas.lean:613), Nat.zero_lt_succ and
Nat.le_add_right (Init/Data/Nat/Basic.lean:369). The old analytic witnesses and
kappa0 can be reused unchanged; the second file supplies the assembly fragment.
These are textual proof candidates only. exact?/apply? and elaboration pending
root, not performed by this read-only audit. No kernel/proof success claimed.

This definition/reader change requires refreshed collector, seals and statement
evidence for the affected owners, plus explicit E-ROUTE/deviation disclosure.
