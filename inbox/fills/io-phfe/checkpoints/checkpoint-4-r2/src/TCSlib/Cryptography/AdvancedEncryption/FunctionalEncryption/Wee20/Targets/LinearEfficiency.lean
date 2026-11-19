/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Raw

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# An additional uniform linear-time encryption target

The deterministic encryption core includes its complete draw as input. The target uses
one finite Turing machine for all numeric dimensions and all public groups, with the
fixed polynomial factor depending only on the security parameter. This is an additional
uniform-machine obligation. The supported-key Boolean-circuit bound is stated separately
in Targets/CircuitEfficiency.

## Main definitions

* `PHFE.linearEncInput`: dimensions and the exact encoded encryption input.
* `LinearEfficient`: one machine and one linear-in-dimensions time bound.

## Main results

* `linearEfficient_iff`: the complete machine-time target reader.

## References

* [GJLS21] R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*,
  EUROCRYPT 2021; full version, Cryptology ePrint Archive, Report 2020/764,
  revision of 3 January 2025, Definitions 4.1, 4.3 and 4.6.
* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive, Report 2020/1420, Sections 2.2 and 3.

-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20

open Complexity Turing TCSlib.Cryptography.Pairing

namespace PHFE

/-- The linear-time encryption input supplies the numeric dimensions, public group, key,
message and complete draw [GJLS21, Definition 4.6, printed p.22]. This is uniform input
layout glue; no dimension, modulus, key or randomness is hard-wired in the machine. -/
def linearEncInput (G : BilinearGen) (ℓ n d κ : ℕ) (pp : PublicParams G κ)
    (pk : Quadratic.MPK G (PolyExpr.const ℓ) (PolyExpr.const n) (PolyExpr.const n) κ pp)
    (x : Fin ((phfeClass (PolyExpr.const ℓ) (PolyExpr.const n) G.wG d).pubLen.eval κ) → Bool)
    (y : Fin ((phfeClass (PolyExpr.const ℓ) (PolyExpr.const n) G.wG d).privLen.eval κ) → Bool)
    (ω : Quadratic.EncDraw G κ pp) : List Bool :=
  NUPPT.advInput κ
    (pairEncode (Candidates.natToList (Nat.size ℓ) ℓ)
      (pairEncode (Candidates.natToList (Nat.size n) n)
        (pairEncode pp.encode
          (pairEncode (List.ofFn (encMPK G (PolyExpr.const ℓ) (PolyExpr.const n) κ pp pk))
            (pairEncode (List.ofFn x)
              (pairEncode (List.ofFn y) (Wire.quadraticEncDraw pp ω)))))))

/-- The encryption layout exposes both dimensions and every deterministic core input. -/
theorem linearEncInput_eq (G : BilinearGen) (ℓ n d κ : ℕ) (pp : PublicParams G κ)
    (pk : Quadratic.MPK G (PolyExpr.const ℓ) (PolyExpr.const n) (PolyExpr.const n) κ pp)
    (x : Fin ((phfeClass (PolyExpr.const ℓ) (PolyExpr.const n) G.wG d).pubLen.eval κ) → Bool)
    (y : Fin ((phfeClass (PolyExpr.const ℓ) (PolyExpr.const n) G.wG d).privLen.eval κ) → Bool)
    (ω : Quadratic.EncDraw G κ pp) :
    linearEncInput G ℓ n d κ pp pk x y ω = NUPPT.advInput κ
      (pairEncode (Candidates.natToList (Nat.size ℓ) ℓ)
        (pairEncode (Candidates.natToList (Nat.size n) n)
          (pairEncode pp.encode
            (pairEncode (List.ofFn (encMPK G (PolyExpr.const ℓ) (PolyExpr.const n) κ pp pk))
              (pairEncode (List.ofFn x)
                (pairEncode (List.ofFn y) (Wire.quadraticEncDraw pp ω))))))) := rfl

end PHFE

/-- One finite Turing machine encrypts in `(ℓ+n)q(κ)` steps uniformly in the numeric
message dimensions, degree and security parameter. This is an additional uniform-machine
obligation; the GJLS21 Definition 4.6 supported-key circuit target is stated separately by
CircuitLinearEfficient. Phase B obligation; not proved in this development.

The positive-size domain is explicit: raw algorithms remain total at zero size, while
this multiplicative bound is required for nonempty messages. The scalar word width is
absorbed into the one polynomial q. -/
def LinearEfficient (G : BilinearGen) : Prop :=
  ∃ M : FinTM Bool, ∃ q : PolyExpr, ∀ (ℓ n d κ : ℕ) (pp : PublicParams G κ)
    (pk : Quadratic.MPK G (PolyExpr.const ℓ) (PolyExpr.const n) (PolyExpr.const n) κ pp)
    (x : Fin ((phfeClass (PolyExpr.const ℓ) (PolyExpr.const n) G.wG d).pubLen.eval κ) → Bool)
    (y : Fin ((phfeClass (PolyExpr.const ℓ) (PolyExpr.const n) G.wG d).privLen.eval κ) → Bool)
    (ω : Quadratic.EncDraw G κ pp), 0 < ℓ + n →
    M.ComputesInTime (PHFE.linearEncInput G ℓ n d κ pp pk x y ω)
      (List.ofFn (PHFE.encCT G (PolyExpr.const n) κ pp
        (PHFE.encCore G (PolyExpr.const ℓ) (PolyExpr.const n) d κ pp pk x y ω))) ((ℓ + n) * q.eval
          κ)

/-- Linear efficiency chooses its one machine and polynomial before every numeric size. -/
theorem linearEfficient_iff (G : BilinearGen) : LinearEfficient G ↔
    ∃ M : FinTM Bool, ∃ q : PolyExpr, ∀ (ℓ n d κ : ℕ) (pp : PublicParams G κ)
      (pk : Quadratic.MPK G (PolyExpr.const ℓ) (PolyExpr.const n) (PolyExpr.const n) κ pp)
      (x : Fin ((phfeClass (PolyExpr.const ℓ) (PolyExpr.const n) G.wG d).pubLen.eval κ) → Bool)
      (y : Fin ((phfeClass (PolyExpr.const ℓ) (PolyExpr.const n) G.wG d).privLen.eval κ) → Bool)
      (ω : Quadratic.EncDraw G κ pp), 0 < ℓ + n →
      M.ComputesInTime (PHFE.linearEncInput G ℓ n d κ pp pk x y ω)
        (List.ofFn (PHFE.encCT G (PolyExpr.const n) κ pp
          (PHFE.encCore G (PolyExpr.const ℓ) (PolyExpr.const n) d κ pp pk x y ω))) ((ℓ + n) * q.eval
            κ) :=
  Iff.rfl

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20
