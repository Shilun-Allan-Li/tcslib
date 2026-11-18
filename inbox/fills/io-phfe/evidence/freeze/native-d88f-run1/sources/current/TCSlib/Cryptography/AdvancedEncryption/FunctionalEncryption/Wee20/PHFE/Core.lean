/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Data

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Honest PHFE cores

The wire-level class is adapted to Wee's typed quadratic construction by total modular
input decoding and by duplicating the private vector. Function keys retain their original
function word. All randomized cores accept one complete finite draw; none samples internally.

## Main definitions

* `Wee20.PHFE.setupCore`, `encCore`, `keyCore`, `dec`: the four honest PHFE cores.

## Main results

Equation readers specify every adapter and the private-input duplication.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, Sections 3.1 and 4.2.
* [GJLS21] R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*,
  EUROCRYPT 2021; full version, Cryptology ePrint Archive, Report 2020/764,
  revision of 3 January 2025, Definitions 4.1-4.2 and 4.6, Section 9.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE

open Complexity Turing TCSlib.Cryptography.Pairing

/-- PHFE setup is the quadratic setup with equal private-vector dimensions
[Wee20, Section 3.1; GJLS21, Section 9]. -/
def setupCore (G : BilinearGen) (ℓ n : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (ω : Quadratic.SetupDraw G ℓ n n κ pp) :
    Quadratic.MPK G ℓ n n κ pp × Quadratic.MSK G ℓ n n κ pp :=
  Quadratic.setupCore G ℓ n n κ pp ω

/-- The setup adapter uses the quadratic core with the two dimensions equal. -/
theorem setupCore_eq (G : BilinearGen) (ℓ n : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) (ω : Quadratic.SetupDraw G ℓ n n κ pp) :
    setupCore G ℓ n κ pp ω = Quadratic.setupCore G ℓ n n κ pp ω := rfl

/-- PHFE encryption decodes the input modulo the drawn order and uses the private
vector in both quadratic slots [GJLS21, Section 9; Wee20, Section 3.1]. -/
def encCore (G : BilinearGen) (ℓ n : PolyExpr) (d κ : ℕ) (pp : PublicParams G κ)
    (pk : Quadratic.MPK G ℓ n n κ pp)
    (x : Fin ((phfeClass ℓ n G.wG d).pubLen.eval κ) → Bool)
    (y : Fin ((phfeClass ℓ n G.wG d).privLen.eval κ) → Bool)
    (ω : Quadratic.EncDraw G κ pp) : Quadratic.CT G n n κ pp :=
  let z := decodePrivate G ℓ n d κ pp y
  Quadratic.encCore G ℓ n n κ pp pk (decodePublic G ℓ n d κ pp x) z z ω

/-- The encryption adapter supplies the same decoded private vector twice. -/
theorem encCore_eq (G : BilinearGen) (ℓ n : PolyExpr) (d κ : ℕ)
    (pp : PublicParams G κ) (pk : Quadratic.MPK G ℓ n n κ pp)
    (x : Fin ((phfeClass ℓ n G.wG d).pubLen.eval κ) → Bool)
    (y : Fin ((phfeClass ℓ n G.wG d).privLen.eval κ) → Bool)
    (ω : Quadratic.EncDraw G κ pp) :
    encCore G ℓ n d κ pp pk x y ω =
      let z := decodePrivate G ℓ n d κ pp y
      Quadratic.encCore G ℓ n n κ pp pk (decodePublic G ℓ n d κ pp x) z z ω := rfl

/-- PHFE key generation retains the original word and generates its typed quadratic key
[Wee20, Section 3.1]. -/
def keyCore (G : BilinearGen) {ℓ n : PolyExpr} {d : ℕ}
    (PG : PartialGarbling.Raw ℓ (n.mul n) (TensorFn ℓ n d)) (κ : ℕ)
    (pp : PublicParams G κ) (msk : Quadratic.MSK G ℓ n n κ pp)
    (f : Fin ((phfeClass ℓ n G.wG d).fnLen.eval κ) → Bool)
    (ω : Linear.KeyDraw G PG κ pp (decodeFunction G ℓ n d κ pp f)) : Key G PG κ pp :=
  ⟨f, Quadratic.keyCore G n n PG κ pp msk (decodeFunction G ℓ n d κ pp f) ω⟩

/-- The key adapter retains its original function word alongside the quadratic key. -/
theorem keyCore_eq (G : BilinearGen) {ℓ n : PolyExpr} {d : ℕ}
    (PG : PartialGarbling.Raw ℓ (n.mul n) (TensorFn ℓ n d)) (κ : ℕ)
    (pp : PublicParams G κ) (msk : Quadratic.MSK G ℓ n n κ pp)
    (f : Fin ((phfeClass ℓ n G.wG d).fnLen.eval κ) → Bool)
    (ω : Linear.KeyDraw G PG κ pp (decodeFunction G ℓ n d κ pp f)) :
    keyCore G PG κ pp msk f ω =
      ⟨f, Quadratic.keyCore G n n PG κ pp msk (decodeFunction G ℓ n d κ pp f) ω⟩ := rfl

/-- PHFE decryption decodes its public input and runs quadratic decryption using the
function retained in the key [GJLS21, Definition 4.1; Wee20, Section 3.1]. -/
def dec (G : BilinearGen) {ℓ n : PolyExpr} {d : ℕ}
    (PG : PartialGarbling.Raw ℓ (n.mul n) (TensorFn ℓ n d)) (κ : ℕ)
    (pp : PublicParams G κ) (sk : Key G PG κ pp)
    (x : Fin ((phfeClass ℓ n G.wG d).pubLen.eval κ) → Bool)
    (ct : Quadratic.CT G n n κ pp) : Option pp.group.GT :=
  some (Quadratic.dec G n n PG κ pp (decodeFunction G ℓ n d κ pp sk.function)
    (decodePublic G ℓ n d κ pp x) sk.quadratic ct)

/-- PHFE decryption returns the displayed typed quadratic value. -/
theorem dec_eq (G : BilinearGen) {ℓ n : PolyExpr} {d : ℕ}
    (PG : PartialGarbling.Raw ℓ (n.mul n) (TensorFn ℓ n d)) (κ : ℕ)
    (pp : PublicParams G κ) (sk : Key G PG κ pp)
    (x : Fin ((phfeClass ℓ n G.wG d).pubLen.eval κ) → Bool)
    (ct : Quadratic.CT G n n κ pp) :
    dec G PG κ pp sk x ct =
      some (Quadratic.dec G n n PG κ pp (decodeFunction G ℓ n d κ pp sk.function)
        (decodePublic G ℓ n d κ pp x) sk.quadratic ct) := rfl

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE
