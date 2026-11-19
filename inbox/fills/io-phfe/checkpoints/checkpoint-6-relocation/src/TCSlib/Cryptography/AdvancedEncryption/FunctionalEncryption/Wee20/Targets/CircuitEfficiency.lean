/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Raw
import TCSlib.Complexity.CircuitComplexity.KarpLiptonSearch

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Supported-key Boolean-circuit linear encryption target

One polynomial bounds circuit size, including input and internal gates, before all numeric
dimensions, degrees
and security parameters. For each supported public parameter and honestly generated
public key, the circuit hard-wires those public values. Its variable input contains
both message words and the complete existing encryption-draw word.

## Main definitions

* `CircuitLinearEfficient`: the supported-key circuit target of GJLS21 Definition 4.6.

## Main results

* `circuitLinearEfficient_iff`: the exact quantifier-order and encoding reader.

## References

* [GJLS21] R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*,
  EUROCRYPT 2021; full version, Cryptology ePrint Archive, Report 2020/764,
  revision of 3 January 2025, Definition 4.6, printed p.22.
* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, Section 3.1.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20

open Complexity TCSlib.Cryptography.Pairing

/-- One polynomial bounds Boolean encryption circuit size, counting input and internal
gates, before all
numeric dimensions, degrees and security parameters [GJLS21, Definition 4.6, printed p.22].
Each supported public parameter and honestly generated public key is hard-wired into
its circuit. The circuit input arity and circuit are chosen before all public/private
message words and complete six-scalar encryption draws. The input-length conjunct
ensures the total bit reader supplies the complete existing paired draw encoding.
The output is exactly the encoded deterministic core ciphertext.

The positive-size domain is explicit. LinearEfficient remains an additional uniform
machine target in its own module. Phase B obligation; not proved in this development.
No circuit, machine, sampler or efficient primitive is constructed here. -/
def CircuitLinearEfficient (G : BilinearGen) : Prop :=
  ∃ q : PolyExpr, ∀ (ℓ n d κ : ℕ) (pp : PublicParams G κ)
    (pk : Quadratic.MPK G (PolyExpr.const ℓ) (PolyExpr.const n) (PolyExpr.const n) κ pp)
    (hHonest : ∃ ρ : Quadratic.SetupDraw G (PolyExpr.const ℓ) (PolyExpr.const n)
        (PolyExpr.const n) κ pp,
      (PHFE.setupCore G (PolyExpr.const ℓ) (PolyExpr.const n) κ pp ρ).1 = pk),
    0 < ℓ + n →
    ∃ N : ℕ, ∃ C : BoolCircuit.MultiDAGCircuit N,
      C.IsFaninTwo ∧ C.size ≤ (ℓ + n) * q.eval κ ∧
        ∀ (x : Fin ((phfeClass (PolyExpr.const ℓ) (PolyExpr.const n) G.wG d).pubLen.eval κ)
              → Bool)
          (y : Fin ((phfeClass (PolyExpr.const ℓ) (PolyExpr.const n) G.wG d).privLen.eval κ)
              → Bool)
          (ω : Quadratic.EncDraw G κ pp),
          let input := List.ofFn x ++ List.ofFn y ++ Wire.quadraticEncDraw pp ω
          input.length = N ∧
            C.eval (fun i => input.getD i.val false) =
              List.ofFn (PHFE.encCT G (PolyExpr.const n) κ pp
                (PHFE.encCore G (PolyExpr.const ℓ) (PolyExpr.const n) d κ pp pk x y ω))

/-- The circuit target chooses its single polynomial before every numeric size, and
chooses each public-parameter/key-specific circuit before all message and draw inputs.

**Proof sketch.** Read the target’s defining quantifiers and conjuncts. -/
theorem circuitLinearEfficient_iff (G : BilinearGen) : CircuitLinearEfficient G ↔
  ∃ q : PolyExpr, ∀ (ℓ n d κ : ℕ) (pp : PublicParams G κ)
    (pk : Quadratic.MPK G (PolyExpr.const ℓ) (PolyExpr.const n) (PolyExpr.const n) κ pp)
    (hHonest : ∃ ρ : Quadratic.SetupDraw G (PolyExpr.const ℓ) (PolyExpr.const n)
        (PolyExpr.const n) κ pp,
      (PHFE.setupCore G (PolyExpr.const ℓ) (PolyExpr.const n) κ pp ρ).1 = pk),
    0 < ℓ + n →
    ∃ N : ℕ, ∃ C : BoolCircuit.MultiDAGCircuit N,
      C.IsFaninTwo ∧ C.size ≤ (ℓ + n) * q.eval κ ∧
        ∀ (x : Fin ((phfeClass (PolyExpr.const ℓ) (PolyExpr.const n) G.wG d).pubLen.eval κ)
              → Bool)
          (y : Fin ((phfeClass (PolyExpr.const ℓ) (PolyExpr.const n) G.wG d).privLen.eval κ)
              → Bool)
          (ω : Quadratic.EncDraw G κ pp),
          let input := List.ofFn x ++ List.ofFn y ++ Wire.quadraticEncDraw pp ω
          input.length = N ∧
            C.eval (fun i => input.getD i.val false) =
              List.ofFn (PHFE.encCT G (PolyExpr.const n) κ pp
                (PHFE.encCore G (PolyExpr.const ℓ) (PolyExpr.const n) d κ pp pk x y ω)) := Iff.rfl

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20
