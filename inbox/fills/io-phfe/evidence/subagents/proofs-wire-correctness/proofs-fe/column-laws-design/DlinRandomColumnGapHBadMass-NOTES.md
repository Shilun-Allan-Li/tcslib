# Random-column hBadMass isolated candidate

Status: proof-only scratch candidate, NOT natively elaborated/sealed/axiom-checked.
No Lean/lake/build/Git/live edit/process operation/extra agent/native search was run by child.

Fragment: DlinRandomColumnGapHBadMass.proof.lean.inc (62 lines). Exactly ONE tactic block,
by plus four-space body for the existing local hBadMass term sorry. No term admission or
new public helper/counting routine/algorithm; <=100 columns. Five local :=?_ goals have
five swap/bullet branches; their actual discharge requires the root's native check.
All other skeleton blocks remain unchanged. Root reports hDet native PASS; hCoords is
pending root native checking. This fragment does not claim the whole random law complete.

## Exact target and proof route

The FULL actual uniform draws remain ab : Fin2->K, rs : Fin2->K, t : K in the original
order. bad(ab,rs,t) is a=0 OR b=0 OR t=r+s. The target remains the exact mass
  1-(1-1/N)^3,
not a union bound or a conditioned/truncated scalar draw. No sampler is built.

Let c=1/N and diagGood(ab) mean BOTH a!=0 and b!=0.
- hDiagMass reuses OneWay.uprob_pi_forall with EXPLICIT (iota:=Fin2) and predicate
  (fun x : K => x != 0), preceded by a fully typed prob_congr converting conjunction
  to Fin.forall_fin_two. Singleton and uprob_not give mass (1-c)^2. This is the existing
  public independent-coordinate count, not a re-proof or copy of Diagonal.hBadMass.
- hMiss(rs) uses the public singleton law DIRECTLY AT THE POINT r+s, then prob_not,
  to give uniform-t miss probability 1-c for every coefficient pair rs. This consumes
  a stronger already-public point-independent result; no explicit translation Equiv
  or a new translation/counting helper is required.
- hFactor uses only the public logical/conditional equations not_or, and_assoc,
  ite_and and ite_mul with unit/zero multiplication. It factors the good-event indicator
  into the diagonal-good indicator and t-miss indicator; no event mass is counted there.
- hGoodMass follows from expect_const_mul and hMiss. hInnerBad is the actual event's
  complement via prob_not/prob_eq_expect and the existing eq_sub_iff_add_eq reader.
- Average the remaining rs-constant integrand using expect_const; use expect_sub and
  expect_const_mul plus hDiagMass. The final cubic is precisely pow_succ', consumed
  through congrArg, not a new polynomial/counting argument. No field_simp or cardinal
  inequality is required; all denominator/cardinality facts are already in the public laws.

Every higher-order probability/independence invocation has the concrete typed predicate
supplied. In particular the critical rewrite is
  OneWay.uprob_pi_forall (iota := Fin 2) (fun x : K => x != 0).
The code uses Lean's actual unicode binder spelling from the published declaration.
There is no unqualified rw guessing that predicate, addressing root's real-law inference
repair. The scalar and pair Bridge readers, scalar singleton points, and prob_congr p/q
are likewise explicit.

The fragment does not depend on hDet/hCoords, group elements, scalar representation
witnesses, matrix rank/image facts, advice/realisers, or later consumer admissions.
The direct loss 4d/p is unchanged and no dlinMatrixSlack is introduced.

## Proof-sketch refinement for integration

The current outer proof sketch/comment says to translate t by -(r+s). This fragment
consumes the existing public singleton law at r+s instead: it already asserts the exact
same shift-independent collision probability. Root may refresh that PROOF SKETCH clause
(and the step comment) to “Use the uniform singleton law at r+s, then the public coordinate
independence and complement laws.” The theorem header and statement prose need no repair.
No such live/source/sketch edit was made by this child.

## Actual static reuse searches / exact nearest APIs

Read the existing local bad definition and hBadMass target in the original random
skeleton; read Games/Probability.lean:146-185, :208-220, :254-275 and :340-344.
Actual rg searches covered prob/uprob conjunction/constant/true/false/if laws, complement,
independent-coordinate and singleton laws, indicator conjunction/ite multiplication,
expectation subtraction/scaling, and the final subtraction/power identities.
No public ProbComp fixed-conjunction probability shortcut was found in the inspected
scope. The nearest inequality OneWay.uprob_and_le_mul is not an exact event identity,
so it is not used. Generic conditional equations cover the needed indicator factor.

Actual used references:
- Games/Probability.lean:208 prob_eq_expect (any decidability instance), :254 prob_congr,
  :267 prob_not, :165 expect_const_mul, :174 expect_const, :340 expect_sub.
- Games/Bridges/Experiments.lean:66 prob_sample_eq_uprob.
- OneWayFunctions/Basic.lean:118 uprob_pi_forall and :144 uprob_eq_one_div_card.
- Foundations/Probability.lean:109 uprob_not (namespace TCSlib.Cryptography).
- Core Init/Data/Fin/Lemmas.lean:925 forall_fin_two.
- Mathlib/Logic/Basic.lean:910 ite_and; Algebra/Notation/Defs.lean:116 ite_mul.
- Core Init/PropLemmas.lean:137 not_or and the public conjunction-association reader.
- Algebra/Group/Basic.lean:741 to_additive eq_sub_iff_add_eq; Group/Defs.lean:616 pow_succ'.

No foreign definition is passed to simp/rw/unfold: bad and diagGood are this proof's own
local predicates, and every other list item is a public theorem. Foreign ProbComp.prob
is read ONLY through its explicit public probability readers, never semantic defeq.
No .eq_1-style generated defining equation or private local Diagonal proof is used.

An exploratory search for eq_sub_comm found no matching source in the first inspected
scope; the code therefore does NOT guess that name, and instead consumes the actually
located eq_sub_iff_add_eq. An initial narrow ite_mul search missed its real home; the
broader static declaration search located and read Algebra/Notation/Defs.lean:116.
No conclusion relies on those no-match explorations. Native validation remains pending.
