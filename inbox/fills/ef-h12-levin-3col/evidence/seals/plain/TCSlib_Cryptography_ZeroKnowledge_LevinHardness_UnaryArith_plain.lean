/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.Gadget
import TCSlib.Cryptography.ZeroKnowledge.EncodingMachines

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
attribute [local irreducible] Complexity.PolyTimeComputable TCSlib.Cryptography.EncodingMachines.divNum TCSlib.Cryptography.EncodingMachines.modNum TCSlib.Cryptography.LevinHardness.clauseLit TCSlib.Cryptography.LevinHardness.litVal

/-!
# Unary arithmetic rows for the 3SAT → 3COL machines

Polynomial-time rows on unary functions `x ↦ 1^(f x)` used by the instance map
(`LevinHardness/ColoringGraph.lean`) and the colouring witness map
(`LevinHardness/ColoringWitness.lean`) of the Levin reduction `3SAT → 3COL` ([AB09, §2.3]):
quotient and remainder (by a unary function or a constant), constant powers, the literal codes
`clauseLit` of a clause code, and the truth value `litVal` of a literal code under an assignment
word. All are read off the public rows of `ZeroKnowledge/EncodingMachines.lean`
(`divNum_poly`, `modNum_poly`, `unaryMul_poly`, `getBit_poly`, …) through their readers.

## Main definitions

None: the file states polynomial-time rows only.

## Main results

* `TCSlib.Cryptography.LevinHardness.unaryDiv_poly`, `unaryMod_poly` — `f / g`, `f % g`.
* `TCSlib.Cryptography.LevinHardness.unaryDivConst_poly`, `unaryModConst_poly` — `f / k`, `f % k`.
* `TCSlib.Cryptography.LevinHardness.unaryPow_poly` — `f ^ n`.
* `TCSlib.Cryptography.LevinHardness.clauseLit_poly` — `clauseLit K c j` at unary `K`, `c`.
* `TCSlib.Cryptography.LevinHardness.litVal_poly` — `litVal` at a unary code.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§2.3.)
-/

namespace TCSlib.Cryptography.LevinHardness

open Complexity EncodingMachines

/-- **Unary quotient**: if `f`, `g` are unary polynomial-time functions, so is
`x ↦ 1^(f x / g x)` (`EncodingMachines.divNum_poly` read through `divNum_eq`). Glue. -/
theorem unaryDiv_poly {f g : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true)
    (hg : PolyTimeComputable fun x => List.replicate (g x) true) :
    PolyTimeComputable fun x => List.replicate (f x / g x) true :=
  (divNum_poly hf hg).congr fun x => by rw [divNum_eq]

/-- **Unary remainder**: if `f`, `g` are unary polynomial-time functions, so is
`x ↦ 1^(f x % g x)` (`EncodingMachines.modNum_poly` read through `modNum_eq`). Glue. -/
theorem unaryMod_poly {f g : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true)
    (hg : PolyTimeComputable fun x => List.replicate (g x) true) :
    PolyTimeComputable fun x => List.replicate (f x % g x) true :=
  (modNum_poly hf hg).congr fun x => by rw [modNum_eq]

/-- **Unary quotient by a constant**: `x ↦ 1^(f x / k)` is polynomial-time for a unary
polynomial-time `f`. Glue. -/
theorem unaryDivConst_poly {f : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true) (k : ℕ) :
    PolyTimeComputable fun x => List.replicate (f x / k) true :=
  unaryDiv_poly hf (unaryConst_poly k)

/-- **Unary remainder by a constant**: `x ↦ 1^(f x % k)` is polynomial-time for a unary
polynomial-time `f`. Glue. -/
theorem unaryModConst_poly {f : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true) (k : ℕ) :
    PolyTimeComputable fun x => List.replicate (f x % k) true :=
  unaryMod_poly hf (unaryConst_poly k)

/-- **Unary constant power**: `x ↦ 1^(f x ^ n)` is polynomial-time for a unary polynomial-time
`f` (`EncodingMachines.unaryMul_poly`, `pow_succ`). Glue. -/
theorem unaryPow_poly {f : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true) (n : ℕ) :
    PolyTimeComputable fun x => List.replicate (f x ^ n) true := by
  induction n with
  | zero => simpa using unaryConst_poly 1
  | succ n ih => simpa only [pow_succ] using unaryMul_poly ih hf

/-- **The literal codes of a clause code are unary polynomial-time**: for unary polynomial-time
`K`, `c`, the map `x ↦ 1^(clauseLit (K x) (c x) j)` is polynomial-time (`clauseLit_eq`:
`c % 2K`, `c / 2K % 2K`, `c / (2K)²`). Glue. -/
theorem clauseLit_poly {K c : List Bool → ℕ}
    (hK : PolyTimeComputable fun x => List.replicate (K x) true)
    (hc : PolyTimeComputable fun x => List.replicate (c x) true) (j : Fin 3) :
    PolyTimeComputable fun x => List.replicate (clauseLit (K x) (c x) j) true := by
  have h2K := unaryMul_poly (unaryConst_poly 2) hK
  simp only [clauseLit_eq]
  fin_cases j
  · simpa using unaryMod_poly hc h2K
  · simpa using unaryMod_poly (unaryDiv_poly hc h2K) h2K
  · simpa using unaryDiv_poly hc (unaryPow_poly h2K 2)

/-- **The truth value of a unary literal code is a polynomial-time test**: for a unary
polynomial-time code `ℓ` and a polynomial-time assignment word `a`, the map
`x ↦ [litVal (fun v => (a x).getD v false) (ℓ x)]` is polynomial-time (the parity of `ℓ x` by
`unaryModConst_poly`, the variable bit by `EncodingMachines.getBit_poly`, `litVal_eq`). Glue. -/
theorem litVal_poly {ℓ : List Bool → ℕ} {a : List Bool → List Bool}
    (hℓ : PolyTimeComputable fun x => List.replicate (ℓ x) true) (ha : PolyTimeComputable a) :
    PolyTimeComputable fun x => [litVal (fun v => (a x).getD v false) (ℓ x)] := by
  have hpar := eqTest_poly (unaryModConst_poly hℓ 2) (unaryConst_poly 0)
  have hbit := getBit_poly ha (unaryDivConst_poly hℓ 2)
  refine (polyTimeComputable_ite hpar hbit (polyTimeComputable_not hbit)).congr fun x => ?_
  rw [litVal_eq]
  by_cases h : ℓ x % 2 = 0 <;> simp [h]

end TCSlib.Cryptography.LevinHardness
