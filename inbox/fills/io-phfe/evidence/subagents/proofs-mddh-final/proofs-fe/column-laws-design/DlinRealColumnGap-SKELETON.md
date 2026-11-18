# Real canonical column law: one-block skeleton

STATUS: SCRATCH SKELETON, NOT A COMPLETE PROOF. Exactly ONE substantive term sorry:
hSurj, the surjectivity of the canonical base transpose when either diagonal is nonzero.
All other steps are drafted without term admissions but have NOT been natively checked.
There are seven local :=?_ goals and seven swap/bullet branches; their actual discharge
is unverified until the root runs Lean. No Lean/lake/build/Git/live edit/process operation,
extra agent, or native search was run by this child.

Candidate: DlinRealColumnGap.skeleton.lean.inc (139 lines). The exact searched header/prose
from the earlier proposal is preserved. Formal target matches root's valid native probe
DlinRealColumnGapExact.lean.txt; no statement repair is made. One outer tactic block only.
The random-column law is untouched. No new helper proof or public runtime definition exists.

## New helper target: HEADER ONLY, proof forbidden until native reuse probes

DlinBaseSurjective.helper-header.lean.inc proposes exactly:
  dlin_base_transpose_mulVec_surjective {K : Type} [Field K]
    (a b : K) (hab : a != 0 OR b != 0) :
    Function.Surjective (Matrix.mulVec (canonical A(a,b))^T).

There is no Fintype K requirement: this is elementary fixed scalar-matrix geometry.
Only the needed one-way implication is proposed, not a full rank characterization or a
second matrix-image law. Parent was sent this target BEFORE any proof was attempted.
No proof of this helper is supplied. The main skeleton leaves its corresponding local
hSurj admitted and cannot claim a completed/standard-only column law.

Cycle-free home: MatrixDH/ColumnLaws.lean before dlin_real_column_gap_le. Probe imports:
FiniteLinear, Mathlib.Logic.Equiv.Fin.Basic, core Lean.Elab.Tactic.LibrarySearch. No Linear,
Defs, SelfReduction or already-admitted consumer may be imported for this helper probe.

Static geometry search found no specialized canonical-DLIN surjectivity theorem. Nearest
exact general APIs are Matrix.mulVec_surjective_iff_exists_right_inverse (:322) and
vecMul_surjective_iff_exists_left_inverse (:312) in Matrix/NonsingularInverse.lean.
These convert a concrete right-inverse witness into the desired surjectivity; matrix
entry/dot-product readers can verify such a witness after root's exact?/apply? probes.
Potential scalar right-inverse witnesses (design only; no identity proof supplied):
- If a!=0, a 3-by-2 right inverse for A^T has rows (a^-1,-a^-1),(0,0),(0,1).
- If b!=0, one has rows (0,0),(-b^-1,b^-1),(1,0).
A direct preimage of (u,v) is also possible: ((u-v)/a,0,v) or (0,(v-u)/b,u).
These are scalar witnesses over K, not witnesses extracted from any group input.

## Filled-by-inspection skeleton steps

P(ab) is exactly the actual rs/L conditional expectation in the searched statement;
Q is exactly the independent uniform-base/rs expectation. bad(ab) means BOTH a=b=0.
The statement's let-bound A is retained with intro A. A local DecidableEq K, rather than
global classical, suffices for the equality-event case split/indicator. Generic Field K is
already a fixed header instance, so no synthetic Field(ZMod ...) inference is attempted.

- hP0/1 and hQ0/1 consume only expect_nonneg/mono/const and the supplied bounds on H.
- hGood derives either diagonal nonzero from not(bad), invokes admitted hSurj, then for
  each fixed rs calls the ALREADY PROVED expect_sample_matrix_mul_of_mulVec_surjective
  with explicit K/r=2/m=3/c=rows/M=A^T and the transposed H test.
- hLeft/hRight are calls to existing expect_sample_equiv at the published
  Matrix.transposeAddEquiv, not new right-multiplication uniform laws. Published
  transpose_mul / transpose_transpose / transposeAddEquiv_apply rewrite their shapes.
  Matrix.mulVec_mulVec connects the exact response in the header to (L*A)*rs.
  expect_sample_comm restores the stated independent M then rs order.
- hBadMass first uses prob_congr plus core Fin.forall_fin_two to identify a=b=0 with
  the event forall i:Fin2, ab(i)=0. Then it reads prob_eq_expect, Bridge.prob_sample_eq_uprob,
  OneWay.uprob_pi_forall, OneWay.uprob_eq_one_div_card, Fintype.card_fin and one_div_pow.
  There is NO counting, scalar singleton, fiber or pair-product probability proof copied
  from Diagonal.hBadMass. The exact existing generic coordinate law is consumed directly.
- hPoint is zero on good by hGood and at most one on bad from the range bounds.
  abs_expect_sub_le_expect averages it, then explicit expect_const and hBadMass finish.

No sampler/machine, group scalar extraction, rejection draw/decoder, advice interface,
realisability assertion, or complete mddhAdv_le clone is introduced. The loss remains
1/N^2, including rows=0 and characteristic two. The frozen total 4d/p remains unchanged;
no dlinMatrixSlack is added.

## Searches actually run this invocation

Read live FiniteLinear.lean:1-115 and confirmed its exact matrix-image header/body. Parent
reports BOTH finite-linear helpers now native PASS and fully admission-free; that supersedes
the earlier design notes' pending-helper status. Read root's native
DlinRealColumnGapExact.lean.txt and run/results.jsonl. Valid results: exact? rc1 one expected
cannot-close error for each column law; apply? rc0 with only partial wrappers and one
scratch sorry each; no typing errors. The probes exclude all original admitted consumers.

Actual rg name/shape searches:
- dlin/column/canonical/surj/rank and transpose/surjectivity in TCSlib and Mathlib matrix
  files; no direct canonical shape was found in the inspected scope.
- mulVec/vecMul_surjective, matrix row/col/range/span shapes. Read the exact right/left
  inverse characterizations in NonsingularInverse.lean:304-346. ToLin.lean's row/column
  span descriptions (:170/:329) are more general alternatives, not copied or used here.
- Read Games/Probability.lean:304-322 (sample equivalence/commutation), :254 prob_congr,
  :409 abs_expect_sub_le_expect; Bridges/Experiments.lean:60-85 sample/uprob readers.
- Read OneWayFunctions/Basic.lean:118-123 independent-coordinate theorem, whose exact
  namespace/source is retained; the scalar singleton reader is :144.
- Checked Matrix.transposeAddEquiv in Data/Matrix/Basic.lean:791-809, including its
  public @[simps apply] reader; a real downstream use of transposeAddEquiv_apply appears
  in Mathlib/RingTheory/Trace/Basic.lean:372. No .eq_1 or generated defining equation read.
- Read Matrix.mulVec_mulVec in Data/Matrix/Mul.lean:824.
- Core Fin.forall_fin_two at Init/Data/Fin/Lemmas.lean:925; one_div_pow at
  Mathlib/Algebra/Group/Basic.lean:435. These are reused, not re-proved.

An initial probe path RealColumnExact.lean.txt and a Matrix/Defs.lean path did not exist;
actual rg --files inventory supplied DlinRealColumnGapExact.lean.txt and Matrix/Basic.lean.
No conclusion relies on those failed exploratory reads. No native probe was run by child.

## Native focus / remaining honesty limits

First root should type the whole skeleton with hSurj admitted, checking intro of the let,
transpose equivalence apply reader, sample/Fintype alignment and local probability syntax.
Then run the separately requested helper header's exact?/apply? BEFORE its proof. If a
published generic theorem supplies it, use that rather than proving the witness fact.
The remaining hSurj is genuine special-matrix geometry; it is not discharged merely by
citing the generic matrix-image probability theorem. All other steps remain candidate
proof code until root's native checks; no PASS/standard-only claim is made for this skeleton.
