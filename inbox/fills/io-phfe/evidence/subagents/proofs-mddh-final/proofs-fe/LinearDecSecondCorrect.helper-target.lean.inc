-- SEARCH-ONLY PROPOSAL. Do not import this placeholder into its reuse probes.
-- Context: namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.

/-- A known scalar matrix can move through the public-input tensor by the identity
Kronecker block. This is the singleton-column specialization of the mixed-product
law used in [Wee20, §4.2, p.10, (10); AGW20, Appendix A, (32), p.38].

**Proof sketch.** Apply Mathlib's Matrix.mul_kronecker_mul to the identity, the
single-column x matrix, R and the identity. Read the chosen singleton column through
publicTensor_apply and the published matrix/product-index equations. The second
mixed-product specialization uses the one-dimensional identity and gives the right
side after dropping its unique singleton coordinate. Do not reprove the generic
Kronecker mixed-product law. -/
theorem kronecker_mul_publicTensor {p : ℕ+} {l : ℕ} {I J : Type}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (x : Fin l → ZMod (p : ℕ)) (R : Matrix I J (ZMod (p : ℕ))) :
    Matrix.kroneckerMap (fun a b => a * b)
        (1 : Matrix (Fin l) (Fin l) (ZMod (p : ℕ))) R *
      publicTensor (p := p) (M := J) x =
        publicTensor (p := p) (M := I) x * R := sorry
