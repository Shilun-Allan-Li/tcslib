/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Hashing.CollisionResistant
import TCSlib.Cryptography.Candidates.DiscreteLog
import Mathlib.Tactic.Simps.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A collision-resistant hash from discrete logarithms (statement phase)

[PS10, Protocol 142.2]: `Gen(1^n)` outputs `(p, g, y)` with `p` an `n`-bit prime, `g` a
generator of `Z_p^*` and `y` a random element of `Z_p^*`; `h_{p,g,y}(x, b) = y^b g^x mod p`.
Theorem 142.3: under the discrete-log assumption this is a collision-resistant hash that
compresses by one bit.

**The construction on the ch. 2–4 layer.** The group comes from an instance generator
`G : ExpGroupGen V` through the collection's generator `expGen` (indices `⟨p, ⟨m, g⟩⟩`, valid at
every parameter, D10). `y = g^w` for `w` drawn by the collection's domain sampler
(`expSampleRaw`, within `2^{-n}` of uniform on `Z_m`). Consequently `y` is within `2^{-n}`
of uniform on `⟨g⟩`, and, when `m = p − 1` (hypothesis `hV` of the theorem), on `Z_p^*`. Arithmetic is through the bundle
`ArithmeticFP` (D11), as for every ch. 2–4 candidate.

**Source notes.**
- The domain: the source says "an `n`-bit string `x`", but its proof needs `x < p − 1`, since
  `x` and `x + (p − 1)` collide (inventory Thm-142.3). So `D_i` is `{(x, b) : x < m}`, and
  `R_i = Z_p^*`; `|R_i| = p − 1 < 2(p − 1) = |D_i|`, the source's one-bit compression.
- The theorem's assumption is the discrete-log assumption for the full group `Z_p^*` (the
  generator `g` of `Z_p^*`), as in [PS10, Lemma 84.1], not the prime-order subgroup of
  Assumption 52.2.

## Main definitions

* `Authentication.dlHashGenFun`, `dlHashEval`: `Gen` and `h` as string functions.
* `Authentication.dlHash`: Protocol 142.2 as a `CRH`.

## Main results

* `Authentication.dlHash_crh` (Thm 142.3, stated; a `sorry` under the source's sketch).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §5.5.2, Protocol 142.2 and Theorem 142.3 (book pp. 142–143).
-/

namespace TCSlib.Cryptography.Authentication

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Candidates
  TCSlib.Cryptography.NumberTheory TCSlib.Cryptography.Games

variable {V : List Bool → Prop}

/-! ### The string functions -/

/-- The group index `⟨p, ⟨m, g⟩⟩` of `Gen`, from its first `coins_G(n)` coins (the collection's
generator `expGenFun`). -/
def dlHashIdx (G : ExpGroupGen V) (z : List Bool) : List Bool :=
  pairFstD (expGenFun G (NUPPT.layout (NUPPT.inParam z) [] []
    ((NUPPT.inCoins z).take (G.gen.coins.eval (NUPPT.inParam z).length))))

/-- The hash index is the first component of `expGenFun`, run on the parameter and the first
`G.gen.coins.eval |inParam z|` input coins. -/
theorem dlHashIdx_eq (G : ExpGroupGen V) (z : List Bool) :
    dlHashIdx G z =
      pairFstD (expGenFun G (NUPPT.layout (NUPPT.inParam z) [] []
        ((NUPPT.inCoins z).take (G.gen.coins.eval (NUPPT.inParam z).length)))) := rfl

/-- `Gen` on the raw layout: the key `⟨i, y⟩`, with `i` the group index and `y = g^w mod p` for
`w` drawn by the domain sampler from the remaining coins. -/
def dlHashGenFun (G : ExpGroupGen V) (z : List Bool) : List Bool :=
  pairEncode (dlHashIdx G z) (expEval (pairEncode (dlHashIdx G z)
    (expSampleRaw (NUPPT.layout (NUPPT.inParam z) (dlHashIdx G z) []
      ((NUPPT.inCoins z).drop (G.gen.coins.eval (NUPPT.inParam z).length))))))

/-- The raw hash generator pairs `dlHashIdx G z` with the exponentiation of a sample drawn
from the remaining input coins [PS10, Protocol 142.2]. -/
theorem dlHashGenFun_eq (G : ExpGroupGen V) (z : List Bool) :
    dlHashGenFun G z =
      pairEncode (dlHashIdx G z) (expEval (pairEncode (dlHashIdx G z)
        (expSampleRaw (NUPPT.layout (NUPPT.inParam z) (dlHashIdx G z) []
          ((NUPPT.inCoins z).drop (G.gen.coins.eval (NUPPT.inParam z).length)))))) := rfl

/-- `g^x mod p` on `⟨1^n, ⟨⟨i, y⟩, xb⟩⟩`, with `x` the first `n` bits of `xb`. -/
def dlHashPow (z : List Bool) : List Bool :=
  expEval (pairEncode (pairFstD (pairFstD (pairSndD z)))
    ((pairSndD (pairSndD z)).take (pairFstD z).length))

/-- The exponentiation step applies `expEval` to the decoded group index and the first
`|pairFstD z|` exponent bits. -/
theorem dlHashPow_eq (z : List Bool) :
    dlHashPow z =
      expEval (pairEncode (pairFstD (pairFstD (pairSndD z)))
        ((pairSndD (pairSndD z)).take (pairFstD z).length)) := rfl

/-- `y · g^x mod p` on `⟨1^n, ⟨⟨i, y⟩, xb⟩⟩`: one multiplication and one reduction modulo `p`. -/
def dlHashMul (z : List Bool) : List Bool :=
  pairSndD (divModStr (pairEncode
    (mulStr (pairEncode (dlHashPow z) (pairSndD (pairFstD (pairSndD z)))))
    (pairFstD (pairFstD (pairFstD (pairSndD z))))))

/-- The multiplication step takes the remainder of `dlHashPow z` times the decoded `y`,
divided by the decoded modulus `p`. -/
theorem dlHashMul_eq (z : List Bool) :
    dlHashMul z =
      pairSndD (divModStr (pairEncode
        (mulStr (pairEncode (dlHashPow z) (pairSndD (pairFstD (pairSndD z)))))
        (pairFstD (pairFstD (pairFstD (pairSndD z)))))) := rfl

/-- **The hash** `h_{p,g,y}(x, b) = y^b g^x mod p` on `⟨1^n, ⟨⟨i, y⟩, xb⟩⟩`, with `x` the first
`n` bits of `xb` and `b` its bit at position `n`: one modular exponentiation, and for `b = 1` one
multiplication and one reduction modulo `p` (`dlHashMul`), each a numeral of the width of `p`. -/
def dlHashEval (z : List Bool) : List Bool :=
  if ((pairSndD (pairSndD z)).drop (pairFstD z).length).headD false then dlHashMul z
  else dlHashPow z

/-- Hash evaluation uses `dlHashMul z` when the decoded selector bit is true and `dlHashPow z`
otherwise [PS10, Protocol 142.2]. -/
theorem dlHashEval_eq (z : List Bool) :
    dlHashEval z =
      if ((pairSndD (pairSndD z)).drop (pairFstD z).length).headD false then dlHashMul z
      else dlHashPow z := rfl

/-! ### Efficiency -/

/-- The group index of `Gen` is polynomial-time. -/
theorem polyTimeComputable_dlHashIdx (G : ExpGroupGen V) : PolyTimeComputable (dlHashIdx G) := by
  have ht : PolyTimeComputable fun z =>
      (NUPPT.inCoins z).take (G.gen.coins.eval (NUPPT.inParam z).length) := by
    convert (polyTimeComputable_pairTakePoly G.gen.coins).comp
      (NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins) using 1
    funext z
    simp [Function.comp_apply]
  exact polyTimeComputable_pairFstD.comp ((expGenFun_poly G).comp
    (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam
      (polyTimeComputable_const []) (polyTimeComputable_const []) ht))

/-- `Gen` is polynomial-time given the arithmetic bundle. -/
theorem polyTimeComputable_dlHashGenFun (H : ArithmeticFP) (G : ExpGroupGen V) :
    PolyTimeComputable (dlHashGenFun G) := by
  have hi := polyTimeComputable_dlHashIdx G
  have hd := (polyTimeComputable_pairDropPoly G.gen.coins).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins)
  have hw := (polyTimeComputable_expSampleRaw H).comp (NUPPT.polyTimeComputable_layout
    NUPPT.polyTimeComputable_inParam hi (polyTimeComputable_const []) hd)
  have h := hi.pairEncode ((polyTimeComputable_expEval H).comp (hi.pairEncode hw))
  refine (congrArg PolyTimeComputable (?_ : dlHashGenFun G = _)).mpr h
  funext z
  simp only [dlHashGenFun, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]

/-- The exponentiation step is polynomial-time given the arithmetic bundle. -/
theorem polyTimeComputable_dlHashPow (H : ArithmeticFP) : PolyTimeComputable dlHashPow := by
  have ht : PolyTimeComputable fun z => (pairSndD (pairSndD z)).take (pairFstD z).length := by
    convert (polyTimeComputable_pairTakePoly .var).comp
      (polyTimeComputable_pairFstD.pairEncode
        (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)) using 1
    funext z
    simp [Function.comp_apply]
  have h := (polyTimeComputable_expEval H).comp (((polyTimeComputable_pairFstD.comp
    polyTimeComputable_pairFstD).comp polyTimeComputable_pairSndD).pairEncode ht)
  refine (congrArg PolyTimeComputable (?_ : dlHashPow = _)).mpr h
  funext z
  simp only [dlHashPow, Function.comp_apply]

/-- The multiplication step is polynomial-time given the arithmetic bundle. -/
theorem polyTimeComputable_dlHashMul (H : ArithmeticFP) : PolyTimeComputable dlHashMul := by
  have hp := polyTimeComputable_dlHashPow H
  have hy := (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD).comp
    polyTimeComputable_pairSndD
  have hP := ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).comp
    polyTimeComputable_pairFstD).comp polyTimeComputable_pairSndD
  have h := polyTimeComputable_pairSndD.comp
    (H.divMod.comp ((H.mul.comp (hp.pairEncode hy)).pairEncode hP))
  refine (congrArg PolyTimeComputable (?_ : dlHashMul = _)).mpr h
  funext z
  simp only [dlHashMul, Function.comp_apply]

/-- The hash is polynomial-time given the arithmetic bundle. -/
theorem polyTimeComputable_dlHashEval (H : ArithmeticFP) : PolyTimeComputable dlHashEval := by
  have hq := polyTimeComputable_pairFstD.pairEncode
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hb₀ := polyTimeComputable_headD.comp ((polyTimeComputable_pairDropPoly .var).comp hq)
  have hb : PolyTimeComputable fun z =>
      [((pairSndD (pairSndD z)).drop (pairFstD z).length).headD false] := by
    refine (congrArg PolyTimeComputable (?_ : (fun z =>
      [((pairSndD (pairSndD z)).drop (pairFstD z).length).headD false]) = _)).mpr hb₀
    funext z
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var]
  exact polyTimeComputable_ite
    (p := fun z => ((pairSndD (pairSndD z)).drop (pairFstD z).length).headD false)
    (f := dlHashMul) (g := dlHashPow) hb (polyTimeComputable_dlHashMul H)
    (polyTimeComputable_dlHashPow H)

/-! ### The hash family -/

/-- **Protocol 142.2** [PS10] as a `CRH`, for the instance generator `G`: keys `⟨i, y⟩`,
domain `D_i = {(x, b) : x < m}` of `(n + 1)`-bit strings (`x` the first `n` bits, read as a
numeral), range `R_i = {y : 0 < y < p}` of `n`-bit numerals, and `h(x, b) = y^b g^x mod p`.
`Gen` uses the coins of `G` and `n²` sampler coins. -/
noncomputable def dlHash (H : ArithmeticFP) (G : ExpGroupGen V) : CRH where
  domLen := .add .var (.const 1)
  rangeLen := .var
  gen := NUPPT.ofPolyTimeUniform (polyTimeComputable_dlHashGenFun H G)
    (.add G.gen.coins (.mul .var .var))
  eval := dlHashEval
  inDom n k x := decide (listToNat ((List.ofFn x).take n) < dlM (pairFstD k))
  inRange _ k y := decide (0 < listToNat (List.ofFn y) ∧ listToNat (List.ofFn y) < dlP (pairFstD k))
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  eval_poly := polyTimeComputable_dlHashEval H

attribute [simps (config := { isSimp := false }) domLen rangeLen gen eval inDom inRange] dlHash

/-- **Theorem 142.3: Protocol 142.2 is a collision-resistant hash compressing by one bit**
[PS10, Theorem 142.3], under the discrete-log assumption for an instance generator of the full
groups `Z_p^*` (`m = p − 1`).

**Proof sketch** (the source's, with its gap closed).
1. *Compression.* From `G.n₀` on, the index is valid with `n`-bit numerals, so
   `|D_i| = 2m = 2(p − 1)` and `|R_i| = p − 1`, and `y^b g^x mod p` is a unit (`g` and `y` are
   coprime to `p`): `h` maps `D_i` into `R_i`.
2. *A collision has `b ≠ b'`.* If `b = b'`, then `g^x = g^{x'}` with `x, x' < m`, so `x = x'`
   (`expF_injective`), and the two inputs are equal.
3. *The reduction.* `B(1^n, ⟨i, g^z⟩)` runs `A` on the key `⟨i, g^z⟩` and, from a collision
   `(x, 0), (x', 1)`, outputs `x − x' mod m`: `g^x = g^z g^{x'}`, so `z = x − x'`. With
   `b = 1` first it outputs `x' − x`.
4. `B` succeeds whenever `A` finds a collision, except that `A`'s key is `g^w` for the
   sampler's `w`, within `2^{-n}` of uniform (`statClose_sampleBelowL`). So `A`'s collision
   probability is at most `B`'s discrete-log probability plus `2^{-n}`: negligible by
   `hDL`. -/
theorem dlHash_crh (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i ∧ dlM i = dlP i - 1) (hDL : G.DLHard) :
    (dlHash H G).Compresses ∧ (dlHash H G).CollisionResistant := by
  sorry

end TCSlib.Cryptography.Authentication
