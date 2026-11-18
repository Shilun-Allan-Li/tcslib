import TCSlib.Cryptography.Pairing.Exponents
import TCSlib.Cryptography.Pairing.MatrixDH.Parameters
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Defs
set_option autoImplicit false
set_option diagnostics true
open Complexity TCSlib.Cryptography.Pairing
open TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
example (G : BilinearGen) {l n : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw l n Fn) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) :
    Fintype (PG.TIdx κ pp.orderParam f ⊕ Fin (n.eval κ)) := inferInstance
example (G : BilinearGen) (κ : ℕ) (pp : PublicParams G κ) :
    (pp.orderParam : ℕ) = pp.group.order := rfl
example (G : BilinearGen) {l n : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw l n Fn) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam)
    (M : Matrix (Fin 3) (PG.TIdx κ pp.orderParam f ⊕ Fin (n.eval κ))
      (ZMod pp.group.order)) :
    Matrix (Fin 3) (PG.MIdx κ pp.orderParam f) (ZMod pp.group.order) :=
  M * (show Matrix _ _ (ZMod pp.group.order) from PG.L0 κ pp.orderParam f)
