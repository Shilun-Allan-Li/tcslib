# Random canonical column law: one-block skeleton

STATUS: SCRATCH SKELETON, NOT A COMPLETE PROOF. Exactly THREE named substantive term
sorries remain: hDet, hCoords and hBadMass. All other steps are drafted without term
admissions but have NOT been natively checked. Nine local :=?_ goals retain nine explicit
swap/bullet branches; native elaboration is required to verify their discharge.
No Lean/lake/build/Git/live edit/process operation/extra agent/native search was run by child.

Candidate: DlinRandomColumnGap.skeleton.lean.inc (181 lines). One tactic block. Exact current
LIVE dlin_random_column_gap_le header and docstring copied unchanged from ColumnLaws.lean,
already valid in root-native header probes. No statement/prose repair is made.
The real-column law is untouched. No new public helper or runtime algorithm is proposed.

## Actual data and exact remaining holes

The theorem's let-bound A remains the canonical three-by-two base. Local C(ab,rs,t) is the
actual augmented scalar matrix
  [[a,0,a*r],[0,b,b*s],[1,1,t]].
P(ab,rs,t) is EXACTLY the conditional L-average from the searched header, and Q is EXACTLY
the independent uniform two-column base / uniform response-vector average. The local bad
predicate is a=0 OR b=0 OR t=r+s. Nothing replaces the canonical random tuple by the alternate
fully-uniform DLIN matrix presentation.

1. hDet: det C = a*b*(t-r-s). This is a special scalar matrix expression. Its intended fill
   MUST consume the public Matrix.det_fin_three and finite-vector entry readers, then ring;
   no generic determinant/rank theorem or new helper proof is supplied here.
2. hCoords: the standard split equivalence applied to L*C equals the PAIR
     (L*A, L*(a*r,b*s,t)).
   This ties the augmented image to the ACTUAL scalar base/response in the header. It may
   use Matrix.mul_apply / mulVec entry readers, the published finite sum and finite-function
   equivalence readers; submatrix/column product readers are reusable alternatives. No
   handwritten new Equiv/inverse or repeated generic matrix-image proof is supplied.
3. hBadMass: the actual ab,rs,t nested average of the bad-event indicator equals
     1-(1-1/N)^3.
   Intended fill: commute rs before ab when useful; at fixed rs translate uniform t by
   -(r+s) via Equiv.addRight + expect_sample_equiv / uprob_comp_equiv. Combine ab and
   translated t with Fin.succFunEquiv, then use OneWay.uprob_pi_forall on the nonzero
   predicate, the existing singleton law and complement law. THIS IS NOT a new counting
   routine, and it MUST NOT copy the local Diagonal.hBadMass counting argument.

These are meaningful missing obligations, not computational algorithms. All three are used
by later assembly. No standard-only proof or native PASS is asserted for this skeleton.
No extra helper appears necessary by the inspected APIs; should one become necessary, its
exact header must receive native exact?/apply? probes before any proof is supplied.

## Existing APIs consumed by the drafted surrounding code

- split is ONLY the composition of existing finite-function equivalences:
    arrowCongr refl (Fin.succFunEquiv K 2), then arrowProdEquivProdArrow.
  It splits each three-entry row into its first two entries and final entry, then separates
  the resulting function-to-product into a pair of functions. No custom inverse is authored.
  F is the original bounded test H composed with this standard split; it is local proof data.
- hSplit uses expect_sample_equiv at split and Bridge.expect_sample_pair to identify a
  uniform three-column output with independent uniform M and v.
- hSurj consumes the hDet hole through Matrix.mulVec_surjective_iff_isUnit,
  Matrix.isUnit_iff_isUnit_det, det_transpose and field isUnit_iff_ne_zero. The three
  nonzero determinant factors follow from not(bad); existing sub_sub/sub_ne_zero readers
  express the last factor. It does NOT introduce another rank assumption.
- hUniform uses the ALREADY PROVED expect_sample_matrix_mul_of_mulVec_surjective with
  explicit K/r=3/m=3/c=rows and M=C^T, then Matrix.transposeAddEquiv, transpose_mul,
  transpose_transpose and public transposeAddEquiv_apply, exactly as the real-column
  candidate's transpose specialization. No right-multiplication uniform law is re-proved.
- hGood applies hCoords under H, then hUniform and hSplit, so no representation inverse
  or scalar witness for an arbitrary group element is involved.
- hP0/1 and hQ0/1 use expect_nonneg/mono/const and the ORIGINAL hH0/hH1 bounds.
- hPoint is zero on not(bad) and at most one on bad. Existing abs_expect_sub_le_expect
  is applied successively over t, rs, ab. Each ignored Q average uses an explicitly
  instantiated expect_const, keeping all computational tests opaque during that rewrite.
  The exact hBadMass then completes the target bound.

Only DecidableEq K is supplied locally; no global classical changes are introduced before
probability computations. Generic Field K is an existing header instance. The loss and
all zero-dimensional cases are unchanged. The direct 4d/p sum already includes zero a/b;
NO dlinMatrixSlack is added, and no full mddhAdv_le/realiser/hybrid statement is restated.

## Static reuse searches / references actually consulted

Read current live ColumnLaws.lean helper/real/random headers and root's valid
DlinRandomColumnGapExact.lean.txt. The parent reports valid exact? expected cannot-close,
apply? partial order/let wrappers only, no typing errors, with FiniteLinear + Fin.Basic
and core LibrarySearch, excluding Linear/Defs/SelfReduction. Both generic FiniteLinear
proofs are now native PASS/admission-free per root. That certifies those dependencies,
NOT this larger skeleton's proof or local obligations.

Actual rg searches included:
- Matrix determinant/unit/surjectivity reader names and their public declarations;
- det_fin_three / det_transpose / isUnit_iff_ne_zero;
- finite-function product/succ equivalences and their application-reader names;
- matrix column/submatrix product readers as possible hCoords reuse;
- sub_sub / sub_ne_zero source shapes, and scalar Equiv.addRight/translation names;
- uniform sample equivalence/commutation, independent-coordinate and complement laws.

Nearest APIs and narrow source reads:
- Matrix.det_fin_three in LinearAlgebra/Matrix/Determinant/Basic.lean:811; det_transpose :199.
- Matrix.isUnit_iff_isUnit_det in Matrix/NonsingularInverse.lean:118;
  mulVec_surjective_iff_isUnit :340; the generic inverse equivalences :312/:322.
- isUnit_iff_ne_zero in Algebra/GroupWithZero/Units/Basic.lean:213.
- Matrix.transposeAddEquiv in Data/Matrix/Basic.lean:801 and its public apply reader;
  transpose_mul in Data/Matrix/Mul.lean:1108.
- Fin.succFunEquiv in Logic/Equiv/Fin/Basic.lean:415;
  Equiv.arrowCongr in Logic/Equiv/Defs.lean:450;
  Equiv.arrowProdEquivProdArrow in Logic/Equiv/Prod.lean:337.
- Data/Matrix/ColumnRowPartitioned.lean:219 mul_fromCols and :201/:208 column-vector readers;
  Data/Matrix/Mul.lean:1117 submatrix_mul and :1127/:1132 equiv variants. These are alternative
  public routes for hCoords, not new locally proved generic identities.
- Games/Probability.lean:304 expect_sample_equiv, :313 expect_sample_comm,
  :267 prob_not, :409 abs_expect_sub_le_expect, :174 expect_const;
  Games/Bridges/Experiments.lean:66 sample/uprob and :80 sample pair.
- OneWayFunctions/Basic.lean:118 uprob_pi_forall and :144 singleton probability;
  Foundations/Probability.lean:109 complement and :165 uniform equivalence.

A few searches for generated additive theorem source declarations (sub_sub/addRight names)
did not locate a literal declaration in the first files inspected. They are standard public
additive counterparts; the drafted hSurj's exact scalar-reader shape remains a native focus,
not a claimed inspected complete proof. No missing public probability law is asserted.
No generated defining equation (.eq_1) or foreign definition is passed to simp/rw/unfold.
All explicit reduction lists name local lets/equalities or public theorem readers.

## Root native queue recommendation

First type this skeleton with its three term sorries, isolating structural typing (intro A,
split equivalence, hSurj reader chain, transpose image and successive averaging). Then fill
ONE named hole per invocation after relevant public reuse searches; hDet is elementary,
hCoords is structural, hBadMass consumes the existing generic probability laws. If any
needs a new published helper, stop at its header/probe rather than authoring a generic
counting routine inside this skeleton. This candidate supplies no new helper proof.
