# Random-column hCoords isolated candidate

Status: proof-only SCRATCH CANDIDATE, NOT natively elaborated/sealed/axiom-checked.
No Lean/lake/build/Git/live edit/process operation/extra agent/native search was run by child.

Fragment: DlinRandomColumnGapHCoords.proof.lean.inc. Exactly one tactic block, by followed
by four-space body, for the existing local hCoords term sorry. No term admissions, new
helper/algorithm/sampler or >100-column line. Two refine/show coordinate goals have their
following proofs; only root-native elaboration verifies their discharge.
The rest of DlinRandomColumnGap.skeleton.lean.inc is unchanged. hBadMass is still pending;
hDet has a separate delivered candidate and is not assumed proved here.

Exact context: C is the local 3-by-3 augmented matrix, A the statement's let-bound base,
L an arbitrary rows-by-three scalar matrix, and split is the existing composition
  arrowCongr refl (Fin.succFunEquiv K 2), then arrowProdEquivProdArrow.
Target: split(L*C) = (L*A, L*(a*r,b*s,t)).

## Coordinate proof / exact standard API reading

Prod.ext reduces to the two function components.
For the first component, funext i j and an explicit `show` read the standard Mathlib
succFunEquiv projection: the j-th retained coordinate is (L*C)(i, Fin.castAdd 1 j).
Two applications of the PUBLIC Matrix.mul_apply rewrite both sides as sums over Fin3.
Apply PUBLIC Finset.sum_congr and congrArg of multiplication by L(i,k). The six remaining
special-matrix entry equalities are rfl after fin_cases on k and j. This compares the
already equal first two columns; no generic matrix multiplication/counting result is
re-proved.

For the second component, funext i and an explicit `show` identify the last coordinate
with column 2 of L*C, and the matrix-vector output with the row dot product. The PUBLIC
Matrix.mul_apply' reads that product entry as L(i) dotted with the last column of C.
Function congruence and three literal entry equalities identify this column with
(a*r,b*s,t). No dot-product or mulVec definition is passed to simp/rw/unfold.

## Rule 10 and reduction boundary

The two `show` steps use ONLY the permitted definitional reduction of CORE/MATHLIB
standard equivalences, finite indices, and matrix-vector notation, plus this proof's OWN
local split/A/C lets. No foreign TCSlib definition is read through its body. Core and
Mathlib definitions are not named in any simp/rw/unfold list: the ONLY rw entries are
published Matrix.mul_apply and Matrix.mul_apply'. Literal entry rfl is within the same
explicitly permitted core/Mathlib reduction rule. No .eq_1 generated defining equation,
private lemma, or new handwritten Equiv/inverse is used.

The generic Equiv application readers were inspected, but no nonexistent succFunEquiv
projection theorem is guessed. The proof deliberately uses `show`, which repository policy
explicitly permits for Mathlib definition reduction. If root prefers additional reader
normalization, the existing exact APIs below are available without changing the target.
This is deterministic scalar algebra for arbitrary L, independent of hDet/hGood/hBadMass.
No group element is inverted or assigned a scalar witness. No characteristic/nonzero/row
positivity assumption is added, and the loss/dlinMatrixSlack ledger is unchanged.

## Actual static searches and nearest sources

Read the exact local split/C/A and hCoords target in DlinRandomColumnGap.skeleton.lean.inc.
Read source standard equivalences:
- Logic/Equiv/Fin/Basic.lean:405-417: appendEquiv maps functions to their castAdd/natAdd
  coordinates under its inverse; succFunEquiv is appendEquiv(n,1).symm followed by the
  unique Fin1-coordinate equivalence. The final coordinate is natAdd 2 0 = 2.
- Logic/Equiv/Defs.lean:450-454: arrowCongr maps f to e2 composed with f and e1.symm.
- Logic/Equiv/Prod.lean:337-340: arrowProdEquivProdArrow projects the first/second function.
- Public Equiv.trans_apply / refl_apply were read at Defs.lean:246/:242.

Actual rg searches covered succFunEquiv_apply, arrowProdEquivProdArrow_apply,
arrowCongr_apply; castAdd/natAdd/castSucc equations; matrix mulVec/sum/dotProduct readers;
and submatrix/column-product alternatives. No complete existing hCoords match was found.
The closest algebra readers consumed are Data/Matrix/Mul.lean:293 Matrix.mul_apply and
:299 Matrix.mul_apply'. The exact statements were read. Matrix.mulVec_eq_sum :697 was
inspected as a longer sum/smul alternative but is NOT used. Matrix.vec3_dotProduct in
LinearAlgebra/Matrix/Notation.lean:510 was also inspected but is unnecessary here.

For exact generated PUBLIC reader names (not theorem proving), the EXISTING .ilean JSON
metadata for Equiv/{Defs,Prod,Fin/Basic} was read with Python; no Lean process was started.
It confirms Equiv.arrowProdEquivProdArrow_apply and Equiv.arrowCongr_apply, and contains no
Fin.succFunEquiv_apply/projection declaration among that module's declared references.
The source definition was therefore read to verify the permitted show reduction rather
than fabricate a reader name. This metadata read is discovery only, not a native probe.

Core Fin.castAdd_mk :511 and natAdd_mk :636/natAdd_last :675 in Init/Data/Fin/Lemmas.lean
were inspected as available exact finite-index equations. The chosen entry proof only
needs finite cases and rfl, so no new index-cast helper is created.
A first search for a mulVec_apply theorem found no such declaration; the actual nearest
public reader was mulVec_eq_sum, while the proof uses permitted show to row dot-product.
No missing probability/counting API is asserted.

Root should check the exact show conversions and finite-entry goals in the current
skeleton scope. No proof completion or standard-only status is claimed before that check.
