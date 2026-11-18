# Wee20.Quadratic.signalGroup_exp proof draft

Status: exact-header replacement, inspected but not elaborated. No live source edits,
Lean, lake, build, or Git commands. No helper declarations, new imports, or statement
changes. Parent reports frozen statement HEAD `70b85f9ba83f27393d98fa5bf88505aea3d22a8d`
and published checkpoint 0 `1e77173a7032b57aa22260787711c6c7a1b7596e`; those metadata
were supplied by the parent rather than independently resolved here.

## Deliverable

`QuadraticSignalGroupExp.lean.inc` replaces only the existing admitted body of
`signalGroup_exp`, currently `Wee20/QuadraticCorrect.lean:65`. A Python assertion
matched the complete original header through `:=` against the live file. One tactic
block, no new admitted terms, and maximum line width 88 columns.

## Proof route

Function extensionality exposes a signal coordinate. The existing `signalGroup_eq`
and `signalScalar_eq` readers expose the two canonical sum blocks; `expVec_apply`
reads the known-power encoding. Split the existing inverse `signalCoord` value:

- First block: both sides are precisely the generator raised to the same existing
  private tensor coordinate; the branch closes by the sum case reader.
- Second block: `privateTensor_eq`, `Matrix.kroneckerMap_apply`, and
  `Equiv.symm_apply_apply` reduce its scalar tensor coordinate to `y1 u.1 * s2 u.2`.
  Specializing the existing `BilinearGroup.expVec_tensor_left` to the pair `u` gives
  exactly the required equality. This uses `congrFun`, avoiding duplication of the
  generic modular-power proof.

No inverse encoding, discrete logarithm, scalar witness for an arbitrary group element,
or new tensor representation is introduced. `y1` is already the known scalar vector
in the theorem hypothesis. Empty dimensions are handled by the canonical sum/product
index types without any positive-dimension assumption.

## Dependencies and remaining admission debt

- `Wee20/Quadratic.lean:156`, `signalGroup_eq`: actual group signal algorithm reader.
- Same file :134, `signalScalar_eq`: scalar signal reader.
- `Pairing/Exponents.lean:119`, `BilinearGroup.expVec_apply`: implicit vector coordinate.
- `Classes.lean:244`, `privateTensor_eq`: published canonical scalar tensor reader.
- `Mathlib/LinearAlgebra/Matrix/Kronecker.lean:60`, `Matrix.kroneckerMap_apply`.
- Core/Mathlib `Sum.elim_inl`, `Sum.elim_inr`, `Equiv.symm_apply_apply`, `congrFun`.
- `Pairing/Exponents.lean`, `BilinearGroup.expVec_tensor_left`:
  `(fun ij => B.expVec g a ij.1 ^ (b ij.2).val) =
    B.expVec g (fun ij => a ij.1 * b ij.2)`.

**Explicit retained dependency:** at inspection time the live generic theorem
`expVec_tensor_left` still had an admitted body. Root is integrating Exponents proofs
separately. This draft retains that theorem dependency and does not by itself establish
an admission-free embedding chain. Its body must be completed/validated separately.

Only published algorithm readers are explicitly rewritten; there is no foreign
definition unfolding or generated defining-equation use. Native checking must confirm
normalization across `piDim` widths, canonical-coordinate inverse simplification, and
the imported tensor theorem. No missing public algebra/coordinate reader was found.

## Actual search/read record

Working tree:
`/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange`.

```sh
sed -n '1,230p' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/QuadraticCorrect.lean
rg -n 'theorem.*(expVec|groupDot|groupMul|pair|kronecker|mulVec)|def.*(expVec|groupDot|groupMul)' TCSlib/Cryptography/Pairing/Exponents.lean
rg -n 'privateTensor|quadEval|phfeEval' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Classes.lean
rg -n 'privateTensor|outer|quad|keyCore_eq|encCore_eq|dec_eq|leak_eq|embed' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/Quadratic.lean
sed -n '42,172p' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/Quadratic.lean
sed -n '430,465p' TCSlib/Cryptography/Pairing/Exponents.lean
rg -n 'kroneckerMap_apply|kronecker_apply|add_dotProduct|dotProduct_mulVec|eq_sub_iff_add_eq|eq_sub_iff_add_eq' .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Kronecker.lean .lake/packages/mathlib/Mathlib/Data/Matrix/Mul.lean .lake/packages/mathlib/Mathlib/Algebra/Group/Basic.lean
rg -n 'signalGroup_exp|cross_value_identity|expVec_tensor_right|expVec_tensor_left' TCSlib | head -35
sed -n '105,136p' TCSlib/Cryptography/Pairing/Exponents.lean
rg -n -A 6 -B 3 'theorem expMat_apply|theorem expVec_apply|theorem pow_mul_mod|theorem pow_one_mod|theorem pow_zero_mod' TCSlib/Cryptography/Pairing/Exponents.lean
rg -n -A 14 -B 5 'theorem pow_val_mul|theorem expVec_tensor_left' TCSlib/Cryptography/Pairing/Exponents.lean
sed -n '52,64p' .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Kronecker.lean
sed -n '237,251p' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Classes.lean
rg -n 'cases h.*signalCoord|signalGroup_eq.*signalScalar_eq|Equiv.symm_apply_apply.*kroneckerMap_apply|expVec_tensor_left' TCSlib/Cryptography .lake/packages/mathlib/Mathlib/Data/Matrix | head -30
rg -n -A 9 -B 4 'pow_val_mul' TCSlib/Cryptography/Pairing/Exponents.lean | head -70
rg -n 'lemma pow_val_mul|theorem pow_val_mul' TCSlib/Cryptography/Pairing
```

The searches confirmed the existing tensor theorem exactly matches the second block;
there is no need for a new helper or a second copy of the modular exponent argument.
Other inspected admissions (`mixGroup_exp`, cross tensor/value, full correctness) were
not changed or drafted in this invocation.

## Verification limits

Header equality, width, one tactic block, and absence-of-admission checks passed textually.
Native elaboration and transitive admission accounting remain pending. No false or
unattainable claim was identified in the chosen statement.
