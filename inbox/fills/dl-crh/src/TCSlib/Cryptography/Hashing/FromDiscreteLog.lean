/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Hashing.CollisionResistant
import TCSlib.Cryptography.Candidates.DiscreteLog
import TCSlib.Cryptography.Hashing.FromDiscreteLog.Encoding
import TCSlib.Cryptography.Hashing.FromDiscreteLog.Algebra
import TCSlib.Cryptography.Hashing.FromDiscreteLog.Coins
import TCSlib.Cryptography.Hashing.FromDiscreteLog.Reduction
import TCSlib.Cryptography.Hashing.FromDiscreteLog.Probability
import TCSlib.Cryptography.Hashing.FromDiscreteLog.Sampling
import Mathlib.Tactic.Simps.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A collision-resistant hash from discrete logarithms

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

* `Authentication.dlHash_compresses`: the compression part of Theorem 142.3 (proved).
* `Authentication.dlHash_crh`: Theorem 142.3 (proved).

## Contents

* `FromDiscreteLog.Encoding`: bounded domain/range cardinalities and bit-vector readers.
* `FromDiscreteLog.Algebra`: collision shape and exponent extraction in the unit group.
* `FromDiscreteLog.Coins`: coin splitting through published machine readers.
* `FromDiscreteLog.Reduction`: the efficient collision-to-discrete-log machine.
* `FromDiscreteLog.Probability`: collision acceptance as a uniform average.
* `FromDiscreteLog.Sampling`: the statistical switch to uniform exponents.

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

/-- On generator coins followed by sampler coins, the raw hash index is the instance
generator's output above its threshold and the fixed default index below it. -/
theorem dlHashIdx_layout (G : ExpGroupGen V) (n : ℕ) (r : G.gen.Coins n)
    (s : List Bool) :
    dlHashIdx G (NUPPT.layout (List.replicate n true) [] [] (List.ofFn r ++ s)) =
      if G.n₀ ≤ n then G.gen.runAt n [] r else dlDefaultIndex := by
  have hr : (List.ofFn r).length = G.gen.coins.eval n := by
    rw [List.length_ofFn, NUPPT.coinLen_eq]
  simp only [dlHashIdx_eq, NUPPT.inParam_layout, NUPPT.inCoins_layout,
    List.length_replicate, List.take_left' hr, expGenFun_eq]
  split_ifs with hn
  · rw [pairFstD_pairEncode, NUPPT.Uniform.runAt_eq G.gen_uniform,
      NUPPT.layout_eq, NUPPT.advInput_eq]
  · exact pairFstD_pairEncode _ _

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

/-- Above the threshold, generator coins followed by sampler coins produce the group
index and the exponentiation of the rejection-sampled exponent [PS10, Protocol 142.2]. -/
theorem dlHashGenFun_layout (G : ExpGroupGen V) (n : ℕ) (r : G.gen.Coins n)
    (s : List Bool) (hn : G.n₀ ≤ n) :
    dlHashGenFun G (NUPPT.layout (List.replicate n true) [] [] (List.ofFn r ++ s)) =
      pairEncode (G.gen.runAt n [] r)
        (expEval (pairEncode (G.gen.runAt n [] r)
          (natToList (dlW (G.gen.runAt n [] r))
            ((sampleBelowL (dlM (G.gen.runAt n [] r))
              (Nat.size (dlM (G.gen.runAt n [] r))) n n s).getD 0)))) := by
  have hr : (List.ofFn r).length = G.gen.coins.eval n := by
    rw [List.length_ofFn, NUPPT.coinLen_eq]
  simp only [dlHashGenFun_eq, dlHashIdx_layout, if_pos hn, NUPPT.inParam_layout,
    NUPPT.inCoins_layout, List.length_replicate, List.drop_left' hr, expSampleRaw_eq]
  simp only [NUPPT.inArg_layout]

/-- Above the generator threshold, every raw generated key has the form `⟨i, g^z⟩`
for an exponent in the domain of its valid group index [PS10, Protocol 142.2].

**Proof sketch.** Every accepted rejection-sampler output is below `m`; its fallback zero
is also below the positive group order. Its residue therefore has exactly that value,
so the sampler's numeral is the canonical exponent encoding. -/
theorem dlHashGenFun_key (G : ExpGroupGen V) (hV : ∀ i, V i → ExpValid i)
    (n : ℕ) (r : G.gen.Coins n) (s : List Bool) (hn : G.n₀ ≤ n) :
    ∃ z : ZMod (expOrd (G.gen.runAt n [] r)),
      dlHashGenFun G (NUPPT.layout (List.replicate n true) [] [] (List.ofFn r ++ s)) =
        pairEncode (G.gen.runAt n [] r) (expF (G.gen.runAt n [] r) z) := by
  let i := G.gen.runAt n [] r
  let w := (sampleBelowL (dlM i) (Nat.size (dlM i)) n n s).getD 0
  have hi : ExpValid i := hV _ (G.valid n r hn)
  have hw : w < dlM i := by
    cases hs : sampleBelowL (dlM i) (Nat.size (dlM i)) n n s with
    | none =>
      simpa only [w, hs, Option.getD_none] using ((expValid_iff i).1 hi).2.1
    | some v =>
      simpa only [w, hs, Option.getD_some] using sampleBelowL_lt hs
  let z : ZMod (expOrd i) := (w : ℕ)
  have hz : z.val = w := by
    change ((w : ℕ) : ZMod (expOrd i)).val = w
    rw [ZMod.val_natCast, expOrd_of_valid hi, Nat.mod_eq_of_lt hw]
  refine ⟨z, ?_⟩
  rw [dlHashGenFun_layout G n r s hn, ← expEval_spec i z, expEnc_eq, hz]

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

/-- At a well-formed valid index, the exponentiation part reads the first `n` input bits
and returns the `n`-bit numeral of their power of `g` modulo `p`. -/
theorem dlHashPow_atParam (n : ℕ) (i y : List Bool) (x : Fin (n + 1) → Bool)
    (hi : ExpValid i) (hw : WellFormedIndex n i)
    (hx : listToNat ((List.ofFn x).take n) < dlM i) :
    dlHashPow (atParam n (pairEncode (pairEncode i y) (List.ofFn x))) =
      natToList n (dlG i ^ listToNat ((List.ofFn x).take n) % dlP i) := by
  have he : expEnc i
      ((listToNat ((List.ofFn x).take n) : ℕ) : ZMod (expOrd i)) =
      (List.ofFn x).take n := by
    rw [expEnc_eq, hw.dlW_eq, ZMod.val_natCast, expOrd_of_valid hi,
      Nat.mod_eq_of_lt hx]
    have hcanon := natToList_length_listToNat ((List.ofFn x).take n)
    simpa only [List.length_take, List.length_ofFn,
      Nat.min_eq_left (Nat.le_succ n)] using hcanon
  have hs := expEval_spec i
    ((listToNat ((List.ofFn x).take n) : ℕ) : ZMod (expOrd i))
  rw [he, expF_eq, hw.dlW_eq, ZMod.val_natCast, expOrd_of_valid hi,
    Nat.mod_eq_of_lt hx] at hs
  simpa only [dlHashPow_eq, atParam_eq, pairFstD_pairEncode,
    pairSndD_pairEncode, List.length_replicate] using hs

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

/-- The multiplication part returns the `n`-bit numeral of the power of `g` times the
key element, reduced modulo `p`, at a valid well-formed index. -/
theorem dlHashMul_atParam (n : ℕ) (i y : List Bool) (x : Fin (n + 1) → Bool)
    (hi : ExpValid i) (hw : WellFormedIndex n i)
    (hx : listToNat ((List.ofFn x).take n) < dlM i) :
    dlHashMul (atParam n (pairEncode (pairEncode i y) (List.ofFn x))) =
      natToList n
        ((dlG i ^ listToNat ((List.ofFn x).take n) % dlP i * listToNat y) % dlP i) := by
  have hw' : (pairFstD i).length = n := by
    obtain ⟨a, b, c, he, ha, _, _⟩ := (wellFormedIndex_iff n i).1 hw
    rw [he, pairFstD_pairEncode]
    exact ha
  have hp : dlP i < 2 ^ n := by
    simpa only [hw.dlW_eq] using dlP_lt_two_pow i
  have hpow : dlG i ^ listToNat ((List.ofFn x).take n) % dlP i < 2 ^ n :=
    (Nat.mod_lt _ ((expValid_iff i).1 hi).1.pos).trans hp
  rw [dlHashMul_eq, dlHashPow_atParam n i y x hi hw hx]
  simp only [atParam_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    divModStr_pairEncode, listToNat_mulStr, hw']
  rw [← dlP_eq i, listToNat_natToList hpow]

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

/-- Hash evaluation at a valid well-formed index is the `n`-bit numeral of `g^x mod p`
for selector false, and of `(g^x mod p) y mod p` for selector true
[PS10, Protocol 142.2]. -/
theorem dlHashEval_atParam (n : ℕ) (i y : List Bool) (x : Fin (n + 1) → Bool)
    (hi : ExpValid i) (hw : WellFormedIndex n i)
    (hx : listToNat ((List.ofFn x).take n) < dlM i) :
    dlHashEval (atParam n (pairEncode (pairEncode i y) (List.ofFn x))) =
      natToList n (if x (Fin.last n) then
        (dlG i ^ listToNat ((List.ofFn x).take n) % dlP i * listToNat y) % dlP i
        else dlG i ^ listToNat ((List.ofFn x).take n) % dlP i) := by
  rw [dlHashEval_eq, dlHashMul_atParam n i y x hi hw hx,
    dlHashPow_atParam n i y x hi hw hx]
  simp only [atParam_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate, FromDiscreteLog.inputWord_drop, List.headD_cons]
  split_ifs <;> rfl

/-- For the key element `g^z`, evaluation writes the residue of the unit
`(if b then g^z else 1) * g^x`, where `x` is the exponent prefix and `b` is the last bit
[PS10, Protocol 142.2]. -/
theorem dlHashEval_expF (n : ℕ) (i : List Bool) (z : ZMod (expOrd i))
    (x : Fin (n + 1) → Bool) (hi : ExpValid i) (hw : WellFormedIndex n i)
    (hx : listToNat ((List.ofFn x).take n) < dlM i) :
    dlHashEval (atParam n (pairEncode (pairEncode i (expF i z)) (List.ofFn x))) =
      natToList n
        (((if x (Fin.last n) then expUnit hi ^ z.val else 1) *
          expUnit hi ^ listToNat ((List.ofFn x).take n) : (ZMod (dlP i))ˣ) :
            ZMod (dlP i)).val := by
  have hp : dlP i < 2 ^ n := by
    simpa only [hw.dlW_eq] using dlP_lt_two_pow i
  have hz : dlG i ^ z.val % dlP i < 2 ^ n :=
    (Nat.mod_lt _ ((expValid_iff i).1 hi).1.pos).trans hp
  rw [dlHashEval_atParam n i (expF i z) x hi hw hx, expF_eq, hw.dlW_eq,
    listToNat_natToList hz]
  cases hb : x (Fin.last n)
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul,
      FromDiscreteLog.expUnit_pow_val]
  · simp only [↓reduceIte, Units.val_mul, ZMod.val_mul,
      FromDiscreteLog.expUnit_pow_val]
    rw [Nat.mul_comm]

/-- Equal evaluations on two distinct domain inputs force different selectors and reveal
the challenge exponent as the corresponding difference modulo `m`
[PS10, proof of Theorem 142.3].

**Proof sketch.** Evaluation writes the residue of the associated unit. Equal fixed-width
numerals therefore give equal units. The unit-group collision lemma rules out equal
selectors and extracts the unique exponent residue. -/
theorem dlHashEval_collision (n : ℕ) (i : List Bool) (z : ZMod (expOrd i))
    (x x' : Fin (n + 1) → Bool) (hi : ExpValid i) (hw : WellFormedIndex n i)
    (hx : listToNat ((List.ofFn x).take n) < dlM i)
    (hx' : listToNat ((List.ofFn x').take n) < dlM i) (hne : x ≠ x')
    (hc : dlHashEval (atParam n (pairEncode (pairEncode i (expF i z)) (List.ofFn x))) =
      dlHashEval (atParam n (pairEncode (pairEncode i (expF i z)) (List.ofFn x')))) :
    x (Fin.last n) ≠ x' (Fin.last n) ∧ z.val =
      if x (Fin.last n) then
        (listToNat ((List.ofFn x').take n) +
          (dlM i - listToNat ((List.ofFn x).take n))) % dlM i
      else (listToNat ((List.ofFn x).take n) +
          (dlM i - listToNat ((List.ofFn x').take n))) % dlM i := by
  haveI : NeZero (dlP i) := ⟨((expValid_iff i).1 hi).1.ne_zero⟩
  have hp : dlP i < 2 ^ n := by
    simpa only [hw.dlW_eq] using dlP_lt_two_pow i
  have hbound (u : (ZMod (dlP i))ˣ) : (u : ZMod (dlP i)).val < 2 ^ n :=
    (ZMod.val_lt _).trans hp
  rw [dlHashEval_expF n i z x hi hw hx, dlHashEval_expF n i z x' hi hw hx'] at hc
  have hv := natToList_injOn (hbound _) (hbound _) hc
  have hu := Units.ext (ZMod.val_injective (dlP i) hv)
  have hd : (listToNat ((List.ofFn x).take n), x (Fin.last n)) ≠
      (listToNat ((List.ofFn x').take n), x' (Fin.last n)) := by
    intro he
    exact hne (FromDiscreteLog.inputWord_num_ext
      (congrArg Prod.fst he) (congrArg Prod.snd he))
  exact FromDiscreteLog.unitCollision_extract hi hx hx' z hd hu

/-- Evaluation on a domain input at a valid well-formed key has exactly `n` bits and
reads as a positive residue below `p` [PS10, compression in Theorem 142.3].

**Proof sketch.** The evaluation is the numeral of a unit's residue. A unit has positive
residue below `p`, and the well-formed width is large enough to encode it exactly. -/
theorem dlHashEval_range (n : ℕ) (i : List Bool) (z : ZMod (expOrd i))
    (x : Fin (n + 1) → Bool) (hi : ExpValid i) (hw : WellFormedIndex n i)
    (hx : listToNat ((List.ofFn x).take n) < dlM i) :
    (dlHashEval (atParam n (pairEncode (pairEncode i (expF i z)) (List.ofFn x)))).length = n ∧
      0 < listToNat (dlHashEval (atParam n
        (pairEncode (pairEncode i (expF i z)) (List.ofFn x)))) ∧
      listToNat (dlHashEval (atParam n
        (pairEncode (pairEncode i (expF i z)) (List.ofFn x)))) < dlP i := by
  have hp2 : 2 ≤ dlP i := ((expValid_iff i).1 hi).1.two_le
  haveI : Fact (1 < dlP i) := ⟨by omega⟩
  haveI : NeZero (dlP i) := ⟨by omega⟩
  let u : (ZMod (dlP i))ˣ :=
    (if x (Fin.last n) then expUnit hi ^ z.val else 1) *
      expUnit hi ^ listToNat ((List.ofFn x).take n)
  have hpw : dlP i < 2 ^ n := by
    simpa only [hw.dlW_eq] using dlP_lt_two_pow i
  have hval : (u : ZMod (dlP i)).val < 2 ^ n := (ZMod.val_lt _).trans hpw
  have hu := units_val_mem u
  rw [dlHashEval_expF n i z x hi hw hx]
  change (natToList n (u : ZMod (dlP i)).val).length = n ∧
    0 < listToNat (natToList n (u : ZMod (dlP i)).val) ∧
      listToNat (natToList n (u : ZMod (dlP i)).val) < dlP i
  rw [length_natToList, listToNat_natToList hval]
  exact ⟨rfl, lt_of_lt_of_le Nat.zero_lt_one hu.1, ZMod.val_lt _⟩

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

/-- The hash generator uses the instance generator's coin polynomial plus `n²` sampler
coins [PS10, Protocol 142.2]. -/
theorem dlHash_gen_coins (H : ArithmeticFP) (G : ExpGroupGen V) :
    (dlHash H G).gen.coins = .add G.gen.coins (.mul .var .var) := by
  rw [dlHash_gen, NUPPT.coins_ofPolyTimeUniform]

/-- The hash generator's coins are the instance generator's coins and an independent
`n²`-bit sampler tape [PS10, Protocol 142.2]. -/
noncomputable def dlHash_coinsEquiv (H : ArithmeticFP) (G : ExpGroupGen V) (n : ℕ) :
    (dlHash H G).gen.Coins n ≃ G.gen.Coins n × (Fin (n * n) → Bool) :=
  (FromDiscreteLog.sumCoinsEquiv (dlHash H G).gen (dlHash_gen_coins H G) n).trans
    (Equiv.prodCongr (NUPPT.coinsEquivPoly (A := G.gen) rfl n).symm
      (Equiv.arrowCongr (finCongr (by rw [PolyExpr.eval_mul, PolyExpr.eval_var]))
        (Equiv.refl Bool)))

/-- The hash coin equivalence splits the sum polynomial, identifies its first component
with the generator's coins, and reads the second component as `n²` bits. -/
theorem dlHash_coinsEquiv_eq (H : ArithmeticFP) (G : ExpGroupGen V) (n : ℕ) :
    dlHash_coinsEquiv H G n =
      (FromDiscreteLog.sumCoinsEquiv (dlHash H G).gen (dlHash_gen_coins H G) n).trans
        (Equiv.prodCongr (NUPPT.coinsEquivPoly (A := G.gen) rfl n).symm
          (Equiv.arrowCongr (finCongr (by rw [PolyExpr.eval_mul, PolyExpr.eval_var]))
            (Equiv.refl Bool))) := rfl

/-- Combining a generator tape and a sampler tape concatenates their encoded words. -/
theorem dlHash_coinsEquiv_symm_ofFn (H : ArithmeticFP) (G : ExpGroupGen V) (n : ℕ)
    (r : G.gen.Coins n) (s : Fin (n * n) → Bool) :
    List.ofFn ((dlHash_coinsEquiv H G n).symm (r, s)) = List.ofFn r ++ List.ofFn s := by
  rw [dlHash_coinsEquiv_eq, Equiv.symm_trans_apply, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Equiv.symm_symm, FromDiscreteLog.sumCoinsEquiv_symm_ofFn,
    Prod.map_fst, Prod.map_snd, NUPPT.coinsEquivPoly_ofFn,
    Equiv.arrowCongr_symm, finCongr_symm, Equiv.refl_symm,
    ofFn_arrowCongr_finCongr]

/-- On recombined generator and sampler coins, the hash generator runs its raw function
on their concatenation [PS10, Protocol 142.2]. -/
theorem dlHash_gen_runAt (H : ArithmeticFP) (G : ExpGroupGen V) (n : ℕ)
    (r : G.gen.Coins n) (s : Fin (n * n) → Bool) :
    (dlHash H G).gen.runAt n [] ((dlHash_coinsEquiv H G n).symm (r, s)) =
      dlHashGenFun G (NUPPT.layout (List.replicate n true) [] []
        (List.ofFn r ++ List.ofFn s)) := by
  rw [NUPPT.runAt_eq, dlHash_coinsEquiv_symm_ofFn, dlHash_gen,
    NUPPT.runAtL_ofPolyTimeUniform, NUPPT.advInput_eq, NUPPT.layout_eq]

/-- The discrete-log hash compresses at every parameter above the instance generator's
threshold when its groups are the full unit groups [PS10, Theorem 142.3].

**Proof sketch.** Split a generated key's coins into the instance and sampler tapes. Its
index is valid and well formed, and its key element is a power of the generator. Evaluation
therefore lands in the positive residues. There are `2m` domain inputs and `p - 1 = m`
range values, with `m > 0`. -/
theorem dlHash_compresses (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i ∧ dlM i = dlP i - 1) : (dlHash H G).Compresses := by
  rw [CRH.compresses_iff]
  refine ⟨G.n₀, ?_⟩
  intro n hn rg
  obtain ⟨⟨r, s⟩, rfl⟩ := (dlHash_coinsEquiv H G n).symm.surjective rg
  rw [dlHash_gen_runAt]
  obtain ⟨z, hkey⟩ := dlHashGenFun_key G (fun i hi => (hV i hi).1)
    n r (List.ofFn s) hn
  rw [hkey]
  have hi := (hV _ (G.valid n r hn)).1
  have hmfull := (hV _ (G.valid n r hn)).2
  have hw := G.wellFormed n r hn
  have hp : dlP (G.gen.runAt n [] r) < 2 ^ n := by
    simpa only [hw.dlW_eq] using dlP_lt_two_pow (G.gen.runAt n [] r)
  have hm : dlM (G.gen.runAt n [] r) < 2 ^ n :=
    ((expValid_iff _).1 hi).2.2.1.trans hp
  simp only [dlHash_inDom, dlHash_inRange, CRH.hash_eq, dlHash_eval,
    pairFstD_pairEncode, decide_eq_true_eq]
  simp only [dlHash_domLen, dlHash_rangeLen, PolyExpr.eval_add, PolyExpr.eval_var,
    PolyExpr.eval_const]
  constructor
  · intro x hx
    have hr := dlHashEval_range n _ z x hi hw hx
    rw [ofFn_padFin_of_length hr.1]
    exact hr.2
  · rw [FromDiscreteLog.card_boundedInput n _ hm.le,
      FromDiscreteLog.card_boundedRange n _ ((expValid_iff _).1 hi).1.pos hp.le,
      ← hmfull]
    have hpos := ((expValid_iff _).1 hi).2.1
    omega

/-- The collision test for a raw finder output on key `⟨i, y⟩`: its two padded inputs
are distinct, have exponent prefixes below `m`, and have equal padded hash values
[PS10, Definition 140.1]. -/
def dlHashCollision (n : ℕ) (i y raw : List Bool) : Prop :=
  let xx := splitBits (a := n + 1) (b := n + 1) (padFin ((n + 1) + (n + 1)) raw)
  listToNat ((List.ofFn xx.1).take n) < dlM i ∧
    listToNat ((List.ofFn xx.2).take n) < dlM i ∧ xx.1 ≠ xx.2 ∧
    padFin n (dlHashEval (atParam n (pairEncode (pairEncode i y) (List.ofFn xx.1)))) =
      padFin n (dlHashEval (atParam n (pairEncode (pairEncode i y) (List.ofFn xx.2))))

/-- The raw collision predicate is exactly the domain, distinctness, and equal-hash test
on its two padded output halves. -/
theorem dlHashCollision_iff (n : ℕ) (i y raw : List Bool) :
    dlHashCollision n i y raw ↔
      let xx := splitBits (a := n + 1) (b := n + 1) (padFin ((n + 1) + (n + 1)) raw)
      listToNat ((List.ofFn xx.1).take n) < dlM i ∧
        listToNat ((List.ofFn xx.2).take n) < dlM i ∧ xx.1 ≠ xx.2 ∧
        padFin n (dlHashEval (atParam n (pairEncode (pairEncode i y) (List.ofFn xx.1)))) =
          padFin n (dlHashEval (atParam n (pairEncode (pairEncode i y) (List.ofFn xx.2)))) :=
  Iff.rfl

/-- Above the generator threshold, collision acceptance is the average over instance
coins of the joint probability over sampler and finder coins of the raw collision test
[PS10, key distribution in Theorem 142.3].

**Proof sketch.** Reindex the generator's uniform coins by their two independent tapes,
read its activation, and expose the collision game's fields through their public readers.
Fubini combines the sampler and finder tapes into a product probability. -/
theorem dlHash_collision_accept_eq (H : ArithmeticFP) (G : ExpGroupGen V) (A : NUPPT)
    (n : ℕ) (hn : G.n₀ ≤ n) :
    accept ((dlHash H G).collisionGame A n) =
      uexp (fun r : G.gen.Coins n =>
        uprob (fun rs : (Fin (n * n) → Bool) × A.Coins n =>
          let i := G.gen.runAt n [] r
          let y := expEval (pairEncode i (natToList n
            ((sampleBelowL (dlM i) (Nat.size (dlM i)) n n (List.ofFn rs.1)).getD 0)))
          dlHashCollision n i y (A.runAt n (pairEncode i y) rs.2))) := by
  rw [FromDiscreteLog.collision_accept_eq,
    ← HardcoreBit.uexp_comp_equiv (dlHash_coinsEquiv H G n).symm,
    HardcoreBit.uexp_prod]
  congr 1
  funext r
  rw [uprob_prod]
  congr 1
  funext s
  apply OneWay.uprob_congr
  intro ra
  rw [dlHash_gen_runAt, dlHashGenFun_layout G n r (List.ofFn s) hn]
  have hw := G.wellFormed n r hn
  simp only [dlHashCollision_iff, dlHash_inDom, CRH.hash_eq, dlHash_eval,
    pairFstD_pairEncode, decide_eq_true_eq, hw.dlW_eq]
  simp only [dlHash_domLen, dlHash_rangeLen, PolyExpr.eval_add, PolyExpr.eval_var,
    PolyExpr.eval_const]

/-- Whenever the finder produces a collision on a valid key `⟨i, g^z⟩`, the reduction's
answer decodes to the challenge exponent [PS10, reduction in Theorem 142.3].

**Proof sketch.** Remove the hash-output padding using its proved exact length. The
collision-extraction lemma identifies the postprocessor's modular difference with `z`.
The reduction therefore writes the canonical `n`-bit numeral of `z`, which decodes exactly. -/
theorem dlHash_reduction_success (H : ArithmeticFP) (A : NUPPT) (n : ℕ)
    (i : List Bool) (z : ZMod (expOrd i)) (hi : ExpValid i) (hw : WellFormedIndex n i)
    (r : (FromDiscreteLog.collisionReduction H A).Coins n)
    (hc :
      let xx := splitBits (a := n + 1) (b := n + 1)
        (padFin ((n + 1) + (n + 1)) (A.runAt n (pairEncode i (expF i z))
          (NUPPT.coinsCongr (FromDiscreteLog.collisionReduction_coins H A) n r)))
      listToNat ((List.ofFn xx.1).take n) < dlM i ∧
        listToNat ((List.ofFn xx.2).take n) < dlM i ∧ xx.1 ≠ xx.2 ∧
        padFin n (dlHashEval (atParam n (pairEncode (pairEncode i (expF i z))
          (List.ofFn xx.1)))) =
        padFin n (dlHashEval (atParam n (pairEncode (pairEncode i (expF i z))
          (List.ofFn xx.2))))) :
    ∃ out : Fin n → Bool,
      decodeFin n ((FromDiscreteLog.collisionReduction H A).runAt n
        (pairEncode i (expF i z)) r) = some out ∧ bitsToNat out = z.val := by
  let key := pairEncode i (expF i z)
  let ra := NUPPT.coinsCongr (FromDiscreteLog.collisionReduction_coins H A) n r
  let xx := splitBits (a := n + 1) (b := n + 1)
    (padFin ((n + 1) + (n + 1)) (A.runAt n key ra))
  change listToNat ((List.ofFn xx.1).take n) < dlM i ∧
    listToNat ((List.ofFn xx.2).take n) < dlM i ∧ xx.1 ≠ xx.2 ∧
      padFin n (dlHashEval (atParam n (pairEncode key (List.ofFn xx.1)))) =
        padFin n (dlHashEval (atParam n (pairEncode key (List.ofFn xx.2)))) at hc
  obtain ⟨hx, hx', hne, hhash⟩ := hc
  have heq : dlHashEval (atParam n (pairEncode key (List.ofFn xx.1))) =
      dlHashEval (atParam n (pairEncode key (List.ofFn xx.2))) := by
    have hh := congrArg List.ofFn hhash
    change List.ofFn (padFin n (dlHashEval (atParam n (pairEncode key (List.ofFn xx.1))))) =
      List.ofFn (padFin n (dlHashEval (atParam n (pairEncode key (List.ofFn xx.2))))) at hh
    rw [ofFn_padFin_of_length (dlHashEval_range n i z xx.1 hi hw hx).1,
      ofFn_padFin_of_length (dlHashEval_range n i z xx.2 hi hw hx').1] at hh
    exact hh
  have hz := (dlHashEval_collision n i z xx.1 xx.2 hi hw hx hx' hne heq).2
  have hb := FromDiscreteLog.collisionReduction_runAt H A n key r
  rw [FromDiscreteLog.collisionPost_split n i (expF i z) _ hw] at hb
  have hanswer : (FromDiscreteLog.collisionReduction H A).runAt n key r =
      natToList n z.val := hb.trans (congrArg (natToList n) hz.symm)
  refine ⟨natToBits n z.val, ?_, ?_⟩
  · rw [hanswer, natToList_eq, decodeFin_ofFn]
  · exact bitsToNat_natToBits (by
      simpa only [hw.dlW_eq] using val_lt_two_pow_dlW i z)

/-- For a fixed valid well-formed index and a uniform challenge exponent, the finder's
collision probability is bounded by the reduction's discrete-log success probability
[PS10, reduction in Theorem 142.3].

**Proof sketch.** Reindex the reduction's coins by the finder's equal-length coin tape.
Every collision in the reindexed experiment implies successful decoding of the challenge
exponent by the pointwise reduction theorem. Monotonicity of uniform probability concludes. -/
theorem dlHash_ideal_collision_le (H : ArithmeticFP) (A : NUPPT) (n : ℕ)
    (i : List Bool) (hi : ExpValid i) (hw : WellFormedIndex n i) :
    uprob (fun zr : ZMod (expOrd i) × A.Coins n =>
      dlHashCollision n i (expF i zr.1) (A.runAt n (pairEncode i (expF i zr.1)) zr.2)) ≤
      uprob (fun zr : ZMod (expOrd i) × (FromDiscreteLog.collisionReduction H A).Coins n =>
        ∃ out : Fin n → Bool,
          decodeFin n ((FromDiscreteLog.collisionReduction H A).runAt n
            (pairEncode i (expF i zr.1)) zr.2) = some out ∧ bitsToNat out = zr.1.val) := by
  rw [← uprob_comp_equiv (Equiv.prodCongr (Equiv.refl (ZMod (expOrd i)))
    (NUPPT.coinsCongr (FromDiscreteLog.collisionReduction_coins H A) n))]
  apply uprob_mono
  intro zr hc
  have hh : dlHashCollision n i (expF i zr.1)
      (A.runAt n (pairEncode i (expF i zr.1))
        (NUPPT.coinsCongr (FromDiscreteLog.collisionReduction_coins H A) n zr.2)) := by
    simpa only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_apply] using hc
  exact dlHash_reduction_success H A n i zr.1 hi hw zr.2
    ((dlHashCollision_iff n i (expF i zr.1) _).1 hh)

/-- Above the generator threshold, collision acceptance is at most the concrete
reduction's discrete-log success probability plus `(1/2)^n`
[PS10, probability bound in Theorem 142.3].

**Proof sketch.** Read the honest key distribution as the average over instance coins
and independent sampler/finder tapes. The bounded sampler is within `(1/2)^n` of a
uniform exponent. For the uniform experiment every collision makes the reduction
succeed. Average the pointwise bounds and identify the discrete-log experiment. -/
theorem dlHash_collision_bound (H : ArithmeticFP) (G : ExpGroupGen V)
    (hV : ∀ i, V i → ExpValid i) (A : NUPPT) (n : ℕ) (hn : G.n₀ ≤ n) :
    accept ((dlHash H G).collisionGame A n) ≤
      G.dlProb (FromDiscreteLog.collisionReduction H A) n + (1 / 2 : ℝ) ^ n := by
  rw [dlHash_collision_accept_eq H G A n hn, ExpGroupGen.dlProb_eq]
  calc
    _ ≤ uexp (fun r : G.gen.Coins n =>
        uprob (fun zr : ZMod (expOrd (G.gen.runAt n [] r)) × A.Coins n =>
          dlHashCollision n (G.gen.runAt n [] r) (expF _ zr.1)
            (A.runAt n (pairEncode (G.gen.runAt n [] r) (expF _ zr.1)) zr.2)) +
          (1 / 2 : ℝ) ^ n) := by
      apply HardcoreBit.uexp_mono
      intro r
      have hi := hV _ (G.valid n r hn)
      have hw := G.wellFormed n r hn
      have hp : dlP (G.gen.runAt n [] r) < 2 ^ n := by
        simpa only [hw.dlW_eq] using dlP_lt_two_pow (G.gen.runAt n [] r)
      have hm : dlM (G.gen.runAt n [] r) < 2 ^ n :=
        ((expValid_iff _).1 hi).2.2.1.trans hp
      have hs := FromDiscreteLog.sampleBelowL_uprob_le hi hm
        (ρ := A.Coins n) (fun v ra =>
          let i := G.gen.runAt n [] r
          let y := expEval (pairEncode i (natToList n v))
          dlHashCollision n i y (A.runAt n (pairEncode i y) ra))
      simpa only [FromDiscreteLog.expEval_natToList_val hw] using hs
    _ = uexp (fun r : G.gen.Coins n =>
        uprob (fun zr : ZMod (expOrd (G.gen.runAt n [] r)) × A.Coins n =>
          dlHashCollision n (G.gen.runAt n [] r) (expF _ zr.1)
            (A.runAt n (pairEncode (G.gen.runAt n [] r) (expF _ zr.1)) zr.2))) +
          (1 / 2 : ℝ) ^ n := by
      rw [HardcoreBit.uexp_add, HardcoreBit.uexp_const]
    _ ≤ _ := add_le_add_right (HardcoreBit.uexp_mono fun r =>
      dlHash_ideal_collision_le H A n _ (hV _ (G.valid n r hn))
        (G.wellFormed n r hn)) _

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
  refine ⟨dlHash_compresses H G hV, ?_⟩
  rw [CRH.collisionResistant_iff]
  intro A
  have hhard := (ExpGroupGen.dlHard_iff G).1 hDL
    (FromDiscreteLog.collisionReduction H A)
  have hhalf : Negligible (fun n : ℕ => (1 / 2 : ℝ) ^ n) := by
    simpa only [one_div] using negligible_two_pow_neg
  have hneg : Negligible (fun n => accept ((dlHash H G).collisionGame A n)) := by
    refine (hhard.add hhalf).mono ⟨G.n₀, ?_⟩
    intro n hn
    rw [abs_of_nonneg (accept_nonneg _),
      abs_of_nonneg (add_nonneg (G.dlProb_nonneg _ n) (pow_nonneg (by norm_num) _))]
    exact dlHash_collision_bound H G (fun i hi => (hV i hi).1) A n hn
  exact ⟨_, hneg, fun _ => le_rfl⟩

end TCSlib.Cryptography.Authentication
