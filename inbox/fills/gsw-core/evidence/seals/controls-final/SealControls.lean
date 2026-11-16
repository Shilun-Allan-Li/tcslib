import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Eval
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Symmetric

/-!
Paired Rule 10 seal controls for the gsw-core fill (probe, not library code).

Every `example` is tagged `CTL-<name>-<kind>` in the comment line before it:
* `POS`: reads through a published reader or notation; must pass unsealed and in all four seals.
* `NEG`: unfolds a foreign definition by `rfl`; must pass unsealed and fail exactly once in every
  sealed variant.
* No `PolyExpr.eval` control: `Complexity.PolyExpr` is outside the import closure of every
  owned file (and of this probe), so seals A and B install the same set; the catalogs show it.
* `COE`: a projection coercion (`FinDist`'s `⟨FinDist.prob⟩`); passes unsealed, A_coe, B_coe;
  fails once in strict variants.
The type-level negatives use the five definitions plan §G8 names (`Regev.augmented`,
`LWE.sample`, `Lossy.gadget`, `Randomized.blocksEquiv`, `BitEncoding.codepoint`) and the
owned files' own `gadget`, `Encrypts` and `mul`, which are foreign here.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open Encryption.PublicKey

-- CTL-gadget-POS
example (P : Parameters) (i : Fin (P.lwe.dimension + 1)) (j : Fin P.columns) :
    gadget P i j = ((TrapdoorFunctions.Lossy.gadget P.width (P.lwe.dimension + 1) j i : ℤ) :
      ZMod P.lwe.modulus) := gadget_apply P i j
-- CTL-gadget-NEG
example (P : Parameters) (i : Fin (P.lwe.dimension + 1)) (j : Fin P.columns) :
    gadget P i j = ((TrapdoorFunctions.Lossy.gadget P.width (P.lwe.dimension + 1) j i : ℤ) :
      ZMod P.lwe.modulus) := rfl
-- CTL-mul-POS
example (P : Parameters) (C₁ C₂ : Ciphertext P) :
    mul P C₁ C₂ = C₁ * lift P (decompose P C₂) := mul_eq P C₁ C₂
-- CTL-mul-NEG
example (P : Parameters) (C₁ C₂ : Ciphertext P) :
    mul P C₁ C₂ = C₁ * lift P (decompose P C₂) := rfl
-- CTL-Encrypts-NEG
example (P : Parameters) (t : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) (C : Ciphertext P)
    (h : Encrypts P t 0 0 C) : ∃ e : Fin P.columns → ℤ, (∀ j, (e j).natAbs ≤ 0) ∧
      Matrix.vecMul t C = ((0 : ℤ) : ZMod P.lwe.modulus) • Matrix.vecMul t (gadget P) +
        fun j => (e j : ZMod P.lwe.modulus) := h
-- CTL-augmented-POS
example (P : Parameters) (pk : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension)
    (ZMod P.lwe.modulus) × (Fin P.lwe.samples → ZMod P.lwe.modulus)) :
    Regev.augmented P.lwe pk = Fin.snoc pk.1.transpose pk.2 := Regev.augmented_eq P.lwe pk
-- CTL-augmented-NEG
example (P : Parameters) (pk : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension)
    (ZMod P.lwe.modulus) × (Fin P.lwe.samples → ZMod P.lwe.modulus)) :
    Regev.augmented P.lwe pk = Fin.snoc pk.1.transpose pk.2 := rfl
-- CTL-sample-POS
example (P : Parameters) (χ : LWE.Noise)
    (r : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      ((Fin P.lwe.dimension → ZMod P.lwe.modulus) × (Fin P.lwe.samples → χ.Coins))) :
    (LWE.sample P.lwe χ r).1 = r.1 := LWE.sample_fst P.lwe χ r
-- CTL-sample-NEG
example (P : Parameters) (χ : LWE.Noise)
    (r : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      ((Fin P.lwe.dimension → ZMod P.lwe.modulus) × (Fin P.lwe.samples → χ.Coins))) :
    (LWE.sample P.lwe χ r).1 = r.1 := rfl
-- CTL-lossyGadget-NEG
example (b w : ℕ) (i : Fin (w * b)) (j : Fin w) :
    TrapdoorFunctions.Lossy.gadget b w i j =
      (let jk : Fin w × Fin b := finProdFinEquiv.symm i
       if jk.1 = j then 2 ^ (jk.2 : ℕ) else 0) := rfl
-- CTL-blocksEquiv-NEG
example (n b : ℕ) : Randomized.blocksEquiv n b =
    ((Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans
      (Equiv.curry _ _ _)).trans (Equiv.arrowCongr (Equiv.refl _) (Randomized.bitsEquiv b)) :=
  rfl
-- CTL-codepoint-POS
example (P : Parameters) : LWE.BitEncoding.codepoint P.lwe true =
    if true then ((P.lwe.modulus / 2 : ℕ) : ZMod P.lwe.modulus) else 0 :=
  LWE.BitEncoding.codepoint_eq P.lwe true
-- CTL-codepoint-NEG
example (P : Parameters) : LWE.BitEncoding.codepoint P.lwe true =
    if true then ((P.lwe.modulus / 2 : ℕ) : ZMod P.lwe.modulus) else 0 := rfl
-- CTL-columns-POS
example (P : Parameters) : P.columns = (P.lwe.dimension + 1) * P.width := rfl
-- CTL-coe-COE
example {α : Type} [Fintype α] (d : InformationTheory.FinDist α) (a : α) :
    d a = d.prob a := rfl

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
