/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Correctness of the raw linear PHFE building block

The correctness statements allow arbitrary source-group key matrices. They do not choose
scalar witnesses for their entries. Instead, the partial-garbling reconstruction law is
specialized to scalar basis vectors, giving the coefficient identities needed to cancel
randomness in products of known powers.

## Main definitions

This module introduces no algorithms or new data representations.

## Main results

* `Wee20.Linear.rec_output_eq_eval`, `rec_matrix_eq`: coefficient consequences of the
  supplied raw partial-garbling reconstruction theorem.
* `Wee20.Linear.decFirst_correct`, `decSecond_correct`: equations (9) and (10), with a
  group-valued matrix and its known scalar inputs.
* `Wee20.Linear.pi_dec_eq`, `scheme_raw_correct`: perfect correctness in the target group,
  for every setup, encryption and key-generation draw.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, §4.2, pp. 9–10, (6)–(11).
* [AGW20] M. Abdalla, J. Gong, and H. Wee, *Functional Encryption for Attribute-Weighted
  Sums from k-Lin*, CRYPTO 2020; full version, Cryptology ePrint Archive 2020/762,
  Lemma 2, p. 12, and Appendix A, (29)–(32), pp. 37–38.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear

open Complexity TCSlib.Cryptography.Pairing
open scoped BigOperators Matrix

/-- The output part of reconstruction equals the function value. This is coefficient glue
from the reconstruction law [AGW20, Lemma 2, p. 12].

**Proof sketch.** Apply `PG.reconstruct` with zero draw and a single unit in the private
input. Use Mathlib's single-coordinate dot-product readers on both sides. -/
theorem rec_output_eq_eval (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (j : Fin (n'.eval κ)) :
    PG.recVec κ pp.orderParam f x (Sum.inl j) = PG.eval κ pp.orderParam f x j := sorry

/-- The reconstruction vector cancels every garbling-draw coordinate. This is coefficient
form of the reconstruction law [AGW20, Lemma 2, p. 12; Appendix A, (29), p. 37].

**Proof sketch.** Apply `PG.reconstruct` with zero private input and a single unit draw.
Use `rec_output_eq_eval` for its final draw block; move that term across the equality and
read the remaining coefficient through the single-coordinate dot-product lemmas. -/
theorem rec_matrix_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (x : Fin (ℓ.eval κ) → ZMod pp.group.order) :
    ((show Matrix _ _ (ZMod pp.group.order) from PG.L1 κ pp.orderParam f) *
        (show Matrix _ _ (ZMod pp.group.order) from PartialGarbling.publicTensor (p :=
          pp.orderParam) (M := PG.MIdx κ pp.orderParam f) x) +
      (show Matrix _ _ (ZMod pp.group.order) from PG.L0 κ pp.orderParam f)) *ᵥ (fun u => PG.recVec κ
        pp.orderParam f x (Sum.inr u)) =
        Sum.elim (fun _ => 0) (PG.eval κ pp.orderParam f x) := sorry

/-- The leakage is the product of the supplied group-matrix entries raised to the known
coefficients `z_a f_b(x)` [Wee20, §4, p. 8].

**Proof sketch.** Read `leak_eq`, `groupMulVec_apply` and `groupDot_eq`. Distribute powers
across finite products, use the source-group modular multiplication law, and commute the
two known scalar factors. No exponent of a group element is recovered. -/
theorem leak_product (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (M : Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (z : Fin (zDim.eval κ) → ZMod pp.group.order) :
    leak G PG zDim κ pp f M x z =
      ∏ a, ∏ b, M a b ^ (z a * (show ZMod pp.group.order from PG.eval κ pp.orderParam f x b)).val :=
        sorry

/-- The first decryption block is the group-valued allowed input mask minus the last
coordinates of `sAT` [Wee20, §4.2, p. 10, (9)].

**Proof sketch.** Read the algorithm equations and transport the scalar actions with
`expVec_vecMul`. Apply pairing bilinearity and multiplicativity. The `sAWM` products cancel
entrywise, leaving the known-input action on the arbitrary group matrix and the `T` mask. -/
theorem decFirst_correct (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (M : Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (z : Fin (zDim.eval κ) → ZMod pp.group.order)
    (a : SetupDraw G ℓ zDim κ pp) (s : EncDraw G κ pp) (t : KeyDraw G PG κ pp f) :
    decFirst G PG zDim κ pp f M
        (keyCore G PG zDim κ pp (setupCore G ℓ zDim κ pp a).2 f M t)
        (encCore G ℓ zDim κ pp (setupCore G ℓ zDim κ pp a).1 x
          (pp.group.expVec pp.generator z) s) =
      fun j => pp.group.pair pp.generator (groupVecMul z M j) *
        (pp.group.pair pp.generator pp.generator) ^
          (-(Matrix.vecMul (Matrix.vecMul s a.1) t.1 (Sum.inr j))).val := sorry

/-- The second decryption block is the second partial-garbling block at coins `sAT`
[Wee20, §4.2, p. 10, (10)].

**Proof sketch.** Use the known-scalar matrix and pairing transport laws. The mixed-product
identity `(I⊗R)(x⊗I)=(x⊗I)R` identifies the two `U` terms. Cancel them and the two `V`
terms; the remaining matrix expression is `(sAT)(L1(x⊗I)+L0)`. -/
theorem decSecond_correct (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (M : Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (z : Fin (zDim.eval κ) → ZMod pp.group.order)
    (a : SetupDraw G ℓ zDim κ pp) (s : EncDraw G κ pp) (t : KeyDraw G PG κ pp f) :
    decSecond G PG zDim κ pp f x
        (keyCore G PG zDim κ pp (setupCore G ℓ zDim κ pp a).2 f M t)
        (encCore G ℓ zDim κ pp (setupCore G ℓ zDim κ pp a).1 x
          (pp.group.expVec pp.generator z) s) =
      pp.group.expVecT (pp.group.pair pp.generator pp.generator)
        (Matrix.vecMul (Matrix.vecMul (Matrix.vecMul s a.1) t.1)
          ((show Matrix _ _ (ZMod pp.group.order) from PG.L1 κ pp.orderParam f) *
              (show Matrix _ _ (ZMod pp.group.order) from PartialGarbling.publicTensor (p :=
                pp.orderParam)
                (M := PG.MIdx κ pp.orderParam f) x) + (show Matrix _ _ (ZMod pp.group.order) from
                  PG.L0 κ pp.orderParam f))) := sorry

/-- Π decrypts to `e(g,[zMf(x)^T])` for every honest draw and an arbitrary source-group
matrix `M` [Wee20, §4.2, p. 10, (11)]. This is perfect correctness in the exponent.

**Proof sketch.** Substitute `decFirst_correct` and `decSecond_correct` into `dec_eq`.
Use the two reconstruction coefficient identities to cancel all `sAT` powers and identify
the remaining source-group product with `leak`. Multiplicativity of pairing gives the
claimed target-group value. This proof does not introduce scalar witnesses for `M`. -/
theorem pi_dec_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (M : Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (z : Fin (zDim.eval κ) → ZMod pp.group.order)
    (a : SetupDraw G ℓ zDim κ pp) (s : EncDraw G κ pp) (t : KeyDraw G PG κ pp f) :
    dec G PG zDim κ pp f M x
        (keyCore G PG zDim κ pp (setupCore G ℓ zDim κ pp a).2 f M t)
        (encCore G ℓ zDim κ pp (setupCore G ℓ zDim κ pp a).1 x
          (pp.group.expVec pp.generator z) s) =
      pp.group.pair pp.generator (leak G PG zDim κ pp f M x z) := sorry

/-- The internal raw algorithm bundle inherits perfect correctness for all its draws
[Wee20, §4.2, p. 10, (11)]. It has no efficiency hypothesis.

**Proof sketch.** Read `scheme_raw_eq` to expose its four cores, then apply `pi_dec_eq`. -/
theorem scheme_raw_correct (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (M : Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (z : Fin (zDim.eval κ) → ZMod pp.group.order)
    (a : SetupDraw G ℓ zDim κ pp) (s : EncDraw G κ pp) (t : KeyDraw G PG κ pp f) :
    let S := scheme_raw G PG zDim κ pp
    S.dec f M x (S.keyCore (S.setupCore a).2 f M t)
        (S.encCore (S.setupCore a).1 x (pp.group.expVec pp.generator z) s) =
      pp.group.pair pp.generator (leak G PG zDim κ pp f M x z) := sorry

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear
