/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Data

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial widths of the PHFE representations

The public-key width is linear in the public and private vector dimensions. The ciphertext
has exactly `6n+5` source-group entries, independent of the polynomial degree and garbling
size. Secret and function keys may be larger; the latter use the garbling's uniform node
bound to permit adaptive function descriptions within one fixed width.

## Main definitions

* `Wee20.PHFE.mpkLen`, `mskLen`, `skLen`, `ctLen`, `simStLen`: polynomial representation widths.

## Main results

Evaluation readers expose the exact numeric accounting of these widths.

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

/-- The public key occupies `(16+24n+8ℓ)wG+10` bits in the nested-pair encoding.
This width is linear in the input dimensions [Wee20, Section 3.1]. -/
def mpkLen (G : BilinearGen) (ℓ n : PolyExpr) : PolyExpr :=
  (((PolyExpr.const 16).add ((PolyExpr.const 24).mul n)).add ((PolyExpr.const 8).mul ℓ)).mul G.wG
    |>.add (PolyExpr.const 10)

/-- The public-key width has the displayed numeric evaluation. -/
theorem mpkLen_eval (G : BilinearGen) (ℓ n : PolyExpr) (κ : ℕ) :
    (mpkLen G ℓ n).eval κ =
      (16 + 24 * n.eval κ + 8 * ℓ.eval κ) * G.wG.eval κ + 10 := rfl

/-- The master secret occupies `(8n³+24n+12ℓ+6)wG+6` bits, including the public
matrix metadata [Wee20, Section 3.1]. -/
def mskLen (G : BilinearGen) (ℓ n : PolyExpr) : PolyExpr :=
  (((((PolyExpr.const 8).mul (n.pow 3)).add ((PolyExpr.const 24).mul n)).add
    ((PolyExpr.const 12).mul ℓ)).add (PolyExpr.const 6)).mul G.wG |>.add (PolyExpr.const 6)

/-- The master-secret width has the displayed numeric evaluation. -/
theorem mskLen_eval (G : BilinearGen) (ℓ n : PolyExpr) (κ : ℕ) :
    (mskLen G ℓ n).eval κ =
      (8 * n.eval κ ^ 3 + 24 * n.eval κ + 12 * ℓ.eval κ + 6) * G.wG.eval κ + 6 := rfl

/-- The fixed function-key width includes the original function word, the public matrix,
and the largest allowed garbling. The original function fixes the actual node dimensions
[Wee20, Sections 3.1 and 4.2]. -/
def skLen (G : BilinearGen) {ℓ n : PolyExpr} {d : ℕ}
    (PG : PartialGarbling.Raw ℓ (n.mul n) (TensorFn ℓ n d)) : PolyExpr :=
  (((PolyExpr.const 2).mul (tensorFnLen ℓ (n.mul n) G.wG d)).add
    (((((PolyExpr.const 8).mul (n.pow 3)).add ((PolyExpr.const 6).mul (n.pow 2))).add
      ((((PolyExpr.const 6).mul ℓ).add (PolyExpr.const 8)).mul PG.mBound)).mul G.wG)).add
        (PolyExpr.const 10)

/-- The function-key width has the displayed polynomial node-bound accounting. -/
theorem skLen_eval (G : BilinearGen) {ℓ n : PolyExpr} {d : ℕ}
    (PG : PartialGarbling.Raw ℓ (n.mul n) (TensorFn ℓ n d)) (κ : ℕ) :
    (skLen G PG).eval κ =
      2 * (tensorFnLen ℓ (n.mul n) G.wG d).eval κ +
        (8 * n.eval κ ^ 3 + 6 * n.eval κ ^ 2 +
          (6 * ℓ.eval κ + 8) * PG.mBound.eval κ) * G.wG.eval κ + 10 := rfl

/-- The ciphertext occupies exactly `(6n+5)wG` bits, independent of ℓ and the
public-polynomial degree [Wee20, Section 3.1; GJLS21, Definition 4.6]. -/
def ctLen (G : BilinearGen) (n : PolyExpr) : PolyExpr :=
  (((PolyExpr.const 6).mul n).add (PolyExpr.const 5)).mul G.wG

/-- The ciphertext width has the displayed numeric evaluation. -/
theorem ctLen_eval (G : BilinearGen) (n : PolyExpr) (κ : ℕ) :
    (ctLen G n).eval κ = (6 * n.eval κ + 5) * G.wG.eval κ := rfl

/-- The complete quadratic simulator state has its fixed polynomial wire width.
This is representation glue for the stateful simulators [Wee20, Sections 3.2 and 4.2].
It includes the public matrix, total inverse and both retained ciphertext masks. -/
def simStLen (G : BilinearGen) (ℓ n : PolyExpr) : PolyExpr :=
  (((((PolyExpr.const 8).mul (n.pow 3)).add ((PolyExpr.const 68).mul n)).add
    ((PolyExpr.const 24).mul ℓ)).add (PolyExpr.const 104)).mul G.wG
      |>.add (PolyExpr.const 40)

/-- The simulator-state width is the exact complete nested-word accounting. -/
theorem simStLen_eval (G : BilinearGen) (ℓ n : PolyExpr) (κ : ℕ) :
    (simStLen G ℓ n).eval κ =
      (8 * n.eval κ ^ 3 + 68 * n.eval κ + 24 * ℓ.eval κ + 104) * G.wG.eval κ + 40 := rfl

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE
