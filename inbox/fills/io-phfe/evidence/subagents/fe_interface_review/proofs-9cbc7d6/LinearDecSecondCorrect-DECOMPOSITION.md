# Linear.decSecond_correct: exact scalar-mask decomposition and tensor probe target

Status: structured skeleton, **not a completed proof**. No live source edits, Lean,
lake, build, or Git commands. Its three explicit term-sorry obligations are hMix,
hNumerator and hDenominator. One tactic block only. No new helper has been proved
or installed before root isolated searches.

## Artifacts and header fidelity

- `LinearDecSecondCorrect.skeleton.lean.inc` preserves the full frozen current
  theorem docstring, source tag, proof sketch and header; Python matched the live block.
- `LinearDecSecondCorrect.helper-target.lean.inc` proposes exactly the tensor
  coordinate specialization needed for hMix, with a natural-language statement and sketch.
  This is a statement placeholder for anonymous exact?/apply? probes, not a proof.

All code lines <=100 columns. The proof-local lets name only the already-given scalar
matrices, existing cores and existing tensor expressions; no runtime algorithm,
representation, sampler or public definition is introduced. No hCipher/hKey/other
already-completed proof is changed.

## Exact remaining tensor specialization

For arbitrary finite source/target coordinate types I,J, scalar R:I-by-J and input x:

`kroneckerMap (*) I_l R * publicTensor(J) x = publicTensor(I) x * R`.

This is the needed `(I tensor R)(x tensor I)=(x tensor I)R`, with publicTensor's
single Fin1 column already removed. At the source use I=Fin2, J=PG.MIdx, R=t.2.
Both finite/decidable-equality instances are explicit. It holds at every positive
modulus and permits l=0 or empty I/J. No rank, prime, nonempty or invertibility
assumption is added.

Name/shape searches found no existing publicTensor multiplication/commutation reader.
The generic mixed-product theorem **does** exist, so its proof must not be duplicated.
The gap is only a source-representation specialization through the canonical singleton
coordinate. Root should run isolated exact?/apply? for the exact proposed statement
before any helper proof. Requested probes=2, verified records=0 in this delivery.

Suggested home if no complete match is found: beside publicTensor_apply in the owned
PartialGarbling/Defs module, namespace PartialGarbling. It imports no Linear module,
so LinearCorrect can consume it without a cycle. A generic Mathlib-only alternative
may use an explicit singleton-column matrix and no publicTensor name, but requires
its own exact target/probes before introducing a second wrapper. No such helper is
proposed here.

## Reusable matrix identity references (explicit)

1. Mathlib `LinearAlgebra/Matrix/Kronecker.lean:369`, **Matrix.mul_kronecker_mul**:
   `(A*B) tensor (A'*B') = (A tensor A') * (B tensor B')`.
   This is the complete generic mixed-product primitive over a commutative semiring.
2. Same file :198, **Matrix.kroneckerMapBilinear_mul_mul**, the more general bilinear
   version. Consume the simpler multiplicative specialization above unless necessary.
3. Same file :60, **Matrix.kroneckerMap_apply**, plus :357 one_kronecker_one,
   :359 kronecker_one and :363 one_kronecker for canonical identity specializations.
4. Mathlib `Data/Matrix/Mul.lean:1127`, **Matrix.submatrix_mul_equiv**, if transport
   through the singleton/product coordinate equivalence is shorter than entry reading.
   `Matrix.mul_apply` (:293), `Fintype.sum_prod_type` and `Fin.sum_univ_one` can also
   remove the unique Fin1 coordinate without a new generic reindexing lemma.
5. Published **PartialGarbling.publicTensor_apply** (Defs:75) is the mandatory reader
   for its source tensor entries; do not unfold publicTensor.
6. Mathlib Matrix.mul_assoc (:475), Matrix.add_mul (:349), Matrix.mul_add (:344),
   Matrix.vecMul_vecMul (:818), Matrix.vecMul_add (:745), Matrix.add_vecMul (:750)
   handle all later scalar factorization. No new generic matrix expansion law is needed.

## Skeleton invariants and the completed scalar factorization

Local names are explanatory aliases: X is the supplied public tensor on PG.MIdx,
X2 the tensor on Fin2, H=I_l tensor R, T=t.1, R=t.2, U/V are the supplied setup
matrices and sa=s vecMul A.

The skeleton's hMatrix states exactly:

`(T L1 + U H) X + (T L0 + V R)
 = T (L1 X + L0) + (U X2 + V) R`.

Given hMix, its displayed proof uses only published distribution/association and
commutative addition. This is a proof step inside the one block, with no separate
helper declaration. The outstanding numerical expressions are:

- value = `(sa vecMul T) vecMul (L1 X + L0)`;
- mask = `(sa vecMul (U X2 + V)) vecMul R`.

## Two remaining source-specific pairing obligations

- hNumerator pairs ct.c0 with the combined K2 X / K3 column. Read setupCore_eq,
  encCore_eq, keyCore_eq and use expMat_mul for the groupMatMul action. The known
  scalar key matrix is exactly hMatrix's left side. Proven expVec_vecMul,
  expVec_add / pow_val_add and pair_expVec read the pair as the target base raised
  to sa times that matrix. hMatrix and Matrix.vecMul_add split it into value+mask;
  pow_val_add_GT gives the two displayed factors.
- hDenominator pairs ct.c2 with the known scalar R column. expMat_mul identifies
  the AU public tensor action, expVec_vecMul handles both public matrices, and
  reverse expVec_add combines their product. Scalar vecMul association/distribution
  gives expVec g (sa vecMul (U X2+V)). pair_expVec yields precisely mask.

Both are now ordinary known-scalar transport: Exponents already proves expMat_mul,
expVec_vecMul, expVec_add, pair_expVec and target exponent laws. No new pairing/group
helper is needed. Published expMat_apply and expVec_apply handle column views; use
permitted Mathlib show/rfl steps for vecMul/dot alignment rather than explicit unfolding.

The final skeleton code reads decSecond_eq and expVecT_apply and cancels the common
mask using mul_inv_cancel_right. It only uses the target inverse already present in
decSecond; no inverse algorithm or scalar recovery is introduced.

The arbitrary group matrix M appears in key metadata but not K2/K3/R; z appears in
ct.c1 but not c0/c2. Their original theorem arguments are preserved without witnesses.
No PG reconstruction/privacy/efficiency law, rec_matrix identity, or rank assumption
is used for this block.

## Actual searches and reads

Working tree:
`/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange`.

```sh
sed -n '174,224p' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/LinearCorrect.lean
sed -n '182,241p' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/Linear.lean
sed -n '269,294p' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/Linear.lean
sed -n '63,80p' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/PartialGarbling/Defs.lean
rg -n 'kronecker.*mul|mul.*kronecker|kroneckerMap.*one|one.*kroneckerMap|kroneckerMap.*mulVec|kroneckerMap.*vecMul' .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Kronecker.lean .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Vec.lean | head -70
sed -n '178,224p' .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Kronecker.lean
rg -n 'publicTensor.*kronecker|kronecker.*publicTensor|publicTensor.*mul|mul.*publicTensor|publicTensor_apply' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption TCSlib/Cryptography/Pairing | head -45
sed -n '350,373p' .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Kronecker.lean
rg -n 'submatrix_mul|mul_submatrix|submatrix_one|submatrix.*Equiv|reindex_mul' .lake/packages/mathlib/Mathlib/Data/Matrix/*.lean .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/*.lean | head -50
rg -n 'kronecker_mul_publicTensor|publicTensor_inter|publicTensor.*mul|mul.*publicTensor|kronecker.*publicTensor' TCSlib .lake/packages/mathlib/Mathlib | head -35
rg -n -A 4 -B 2 'theorem add_vecMul|theorem vecMul_add|theorem mul_assoc' .lake/packages/mathlib/Mathlib/Data/Matrix/Mul.lean | head -42
```

The full mixed-product statement was read, not just its name. Current Exponents
transport APIs and matrix-distribution declarations were inspected to distinguish the
single missing coordinate specialization from already-proved generic algebra.

## Validation limits

This is explicitly a skeleton with three visible holes. Static frozen header/prose,
width and one-block checks passed. No helper probe or native proof check was run here.
Root native searches/typechecking and standard-axiom inventory remain pending.
No mathematical obstruction or false claim was found; no statement is weakened.
