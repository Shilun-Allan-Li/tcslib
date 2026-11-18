# Exact fixed min/2 exponent through shared closure

The goal is exactly

  SubexpSmall (min(E*cL,min(E*D*cG,1))/2) (rawAdv A),

with the same common cL,cG as in the all-adversary hypotheses. There is no exponent
chosen separately for the selected realisers or for A. In the later SubexpHard
corollary cL,cG are extracted once before forall A, so the output witness is common.

## Quantifier and prerequisite discipline

For fixed P, pi, A, first obtain omegaL,omegaG from the existing prop41. Only then
read P.Realizable through realizable_iff, LPNRealizable_iff and PRGRealizable_iff,
and obtain BL,BG for those exact advised functions and A's exact coin layout.
Apply the bound universally quantified over BL,BG to their shared-realiser proofs.
This preserves exists advice / forall realisers / forall kappa. It does not claim
prop41 only for one selected machine or let advice depend on its realiser.

These are uses of explicitly unproved M4/M3 prerequisites in a candidate body,
not evidence those prerequisites are correct. No machine is manufactured.

## Reindex the shared decay bounds

Let EL=E*cL, EG=E*D*cG and M=min(EL,min(EG,1)). Stored E>=1 and earlier D_pos,
together with cL,cG>0, imply EL>0, EG>0, and M>0. Also M<=EL,EG,1.

- Apply shared SubexpSmall.comp_of_rpow_le to LPN with a=(E:Real), using the exact
  ell(kappa)=kappa^E equation at threshold zero.
- Apply the same public theorem to PRG with a=(E:Real)*D, using n=ell^D and public
  Real.rpow_mul / rpow_natCast and Nat.cast_pow equations. This gives exactly EG,
  without choosing a smaller unexplained reindexing exponent.

The candidate supplies these schedule equalities through proved owner readers and
existing power theorems. It does not reprove the shared reindexing calculus.

## Explicit exponent budget

Every drop below is strict because M>0; monotone weakening permits equality.
The helper linear inequalities are discharged by arithmetic, not by a copied
subexponential decay proof.

| Term / step | Input exponent | Shared operation | Result exponent |
| --- | --- | --- | --- |
| LPN reindexed | EL | mono_exponent using M<=EL | M |
| Multiply by kappa | M | mul_pow M_pos (7M/8<M) 1 | 7M/8 |
| Multiply by 2 | 7M/8 | const_mul (7M/8)_pos (3M/4<7M/8) 2 | 3M/4 |
| PRG reindexed | EG | mono_exponent using 3M/4<=M<=EG | 3M/4 |
| Pure error majorant 2^-kappa | 1 | subexpSmall_two_pow_neg, const_mul 1_pos (3M/4<1) 2 | 3M/4 |
| LPN factor + PRG | 3M/4 each | add (3M/4)_pos (5M/8<3M/4) | 5M/8 |
| Pure error majorant | 3M/4 | mono_exponent using 5M/8<=3M/4 | 5M/8 |
| Previous sum + error | 5M/8 each | add (5M/8)_pos (M/2<5M/8) | M/2 |

Thus the two additions and the polynomial/constant losses fit the exact frozen
M/2 conclusion. Repeated halving would produce the wrong weaker exponent; it is
neither necessary nor used here.

## Final domination

The decaying majorant is

  U(k)=2*(k^1*LPNadv BL(ell k))+Gadv BG(n k)+2*(2^-k).

At the common Claim4.2 threshold, prop41 and 2*errProb<=2*(2^-k) give rawAdv A k<=U(k).
Read raw advantage through Raw.adv_eq and Games.advantage_nonneg. Then 0<=U follows
from the inequality itself. This allows abs(rawAdv)<=abs(U) without separate proofs
that each assumption advantage or errProb is nonnegative. Shared SubexpSmall.mono
transfers the M/2 decay from U to rawAdv.

No new theorem claiming error-function decay is needed. The pure shared
subexpSmall_two_pow_neg is used directly, and Claim4.2 only appears in the final
eventual inequality. Neither subexpSmall_iff's body nor a custom exponential
absorption argument is unfolded/reproduced.

## Exact public shared API

All names are in TCSlib.Cryptography, at
TCSlib/Cryptography/Foundations/Subexponential.lean.

| Public name | Line | Exact selected role |
| --- | --- | --- |
| SubexpSmall.comp_of_rpow_le | 238 | own-parameter hardness -> exponent multiplied by E or E*D; accepts nonnegative c and positive reindex exponent. |
| SubexpSmall.mono_exponent | 163 | weaken to each chosen common intermediate exponent. |
| SubexpSmall.mul_pow | 204 | kappa^1 hybrid factor, to any strict smaller exponent. |
| SubexpSmall.const_mul | 190 | factor 2, to any strict smaller exponent. |
| SubexpSmall.add | 176 | sum two bounds at a common exponent, to any strict smaller exponent. |
| subexpSmall_two_pow_neg | 258 | exact pure 2^-kappa bound at exponent 1. |
| SubexpSmall.mono | 152 | final eventual domination in absolute value. |
| subexpHard_iff | 279 | common exponent witness before every adversary. |
| SubexpHard.negligible / SubexpSmall.negligible | 286 / 218 | available for deriving ordinary security from a subexponential assumption; not needed to duplicate the raw negligible proof. |
| eventually_const_mul_rpow_mul_two_rpow_neg_le | 132 | underlying shared absorption theorem; closure lemmas above already apply it, so no inline rederivation. |

Auxiliary public Mathlib/Core facts are only positive Nat casts, min order,
Real.rpow_mul (:399), rpow_natCast (:58), Nat.cast_pow, ordinary abs/nonnegative
rewriting and scalar arithmetic. Shared predicate/readers remain opaque.

## Joint conclusions and existence

The joint raw theorems simply pair the proved security consequence, algebraic
complexity and polynomial stretch. Their bodies are explicit terms, with no new
efficiency claim. Existence chooses E=max1 E0, constructs the local Params record
from the supplied d/G/R/rational delta, instantiates hLPN/hR at E and its positive
proof, and returns exactly jlsSPRG_raw with the supplied arbitrary modulus schedule.
It neither assumes LPN for unrelated families nor constructs an efficient primitive.

The seven body candidates and the source-level explanation are unelaborated. The
lead must run the authorized proof checks, overlap probes and axiom/dependency
checks; none is claimed by this preparation.
