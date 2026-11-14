/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Candidates.DiscreteLog

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Recovering a discrete logarithm from a hash collision

The algebraic part of the reduction in Theorem 142.3 works in the group of units.
Equal selector bits force equal bounded exponents. With different selector bits,
the collision determines the challenge exponent as a difference modulo the order.

## Main definitions

There are no new definitions.

## Main results

* `expUnit_pow_val` reads powers of the generator unit as modular exponentiation.
* `unitCollision_selector_ne` rules out a collision with equal selector bits.
* `unitCollision_extract` gives the residue extracted from a collision.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, §5.5.2, proof of Theorem 142.3.
-/

namespace TCSlib.Cryptography.Authentication.FromDiscreteLog

open TCSlib.Cryptography.Candidates

/-- The residue of the generator unit raised to `e` is `g ^ e mod p` at a valid index,
where `g = dlG i` and `p = dlP i`. -/
theorem expUnit_pow_val {i : List Bool} (hi : ExpValid i) (e : ℕ) :
    ((expUnit hi ^ e : (ZMod (dlP i))ˣ) : ZMod (dlP i)).val = dlG i ^ e % dlP i := by
  have hvalid := (expValid_iff i).1 hi
  haveI : NeZero (dlP i) := ⟨hvalid.1.ne_zero⟩
  rw [val_units_pow, coe_expUnit, ZMod.val_natCast,
    Nat.mod_eq_of_lt hvalid.2.2.2.2.1]

/-- If adding `b ≤ m` to a residue `a < m` gives `c` modulo `m`, then adding
`m - b` to `c` recovers `a` modulo `m`. -/
private theorem residue_difference {m a b c : ℕ} (ha : a < m) (hb : b ≤ m)
    (h : Nat.ModEq m (a + b) c) : a = (c + (m - b)) % m := by
  have hh : (a + b + (m - b)) % m = (c + (m - b)) % m :=
    Nat.ModEq.add_right (m - b) h
  have heq : a + b + (m - b) = a + m := by omega
  rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt ha] at hh
  exact hh

/-- In the group of a valid index, `g^a g^b = g^c` with `a,b < m` recovers
`a = (c + (m - b)) mod m`, where `m` is the order of `g`. -/
private theorem residue_of_unit_pow_mul {i : List Bool} (hi : ExpValid i)
    {a b c : ℕ} (ha : a < dlM i) (hb : b < dlM i)
    (h : expUnit hi ^ a * expUnit hi ^ b = expUnit hi ^ c) :
    a = (c + (dlM i - b)) % dlM i := by
  have hp : expUnit hi ^ (a + b) = expUnit hi ^ c := by
    rw [pow_add]
    exact h
  have hm := pow_eq_pow_iff_modEq.1 hp
  rw [orderOf_expUnit hi] at hm
  exact residue_difference ha hb.le hm

/-- A collision between two distinct bounded exponent/selector pairs has different
selector bits [PS10, proof of Theorem 142.3].

**Proof sketch.** With equal selectors, cancel their common unit factor. Read the
remaining powers through their numerals and apply the published injectivity of
exponentiation. The bounded exponent residues, and hence the two pairs, are equal. -/
theorem unitCollision_selector_ne {i : List Bool} (hi : ExpValid i)
    {x x' : ℕ} (hx : x < dlM i) (hx' : x' < dlM i)
    (z : ZMod (expOrd i)) {b b' : Bool}
    (hdistinct : (x, b) ≠ (x', b'))
    (hcollision :
      (if b then expUnit hi ^ z.val else 1) * expUnit hi ^ x =
      (if b' then expUnit hi ^ z.val else 1) * expUnit hi ^ x') : b ≠ b' := by
  intro hb
  subst b'
  have hp : expUnit hi ^ x = expUnit hi ^ x' := mul_left_cancel hcollision
  have hxord : x < expOrd i := by rw [expOrd_of_valid hi]; exact hx
  have hxord' : x' < expOrd i := by rw [expOrd_of_valid hi]; exact hx'
  have hxval : ((x : ℕ) : ZMod (expOrd i)).val = x := ZMod.val_cast_of_lt hxord
  have hxval' : ((x' : ℕ) : ZMod (expOrd i)).val = x' := ZMod.val_cast_of_lt hxord'
  have hnum := congrArg (fun u : (ZMod (dlP i))ˣ => (u : ZMod (dlP i)).val) hp
  change ((expUnit hi ^ x : (ZMod (dlP i))ˣ) : ZMod (dlP i)).val =
    ((expUnit hi ^ x' : (ZMod (dlP i))ˣ) : ZMod (dlP i)).val at hnum
  rw [expUnit_pow_val hi x, expUnit_pow_val hi x'] at hnum
  have hf : expF i ((x : ℕ) : ZMod (expOrd i)) =
      expF i ((x' : ℕ) : ZMod (expOrd i)) := by
    rw [expF_eq, expF_eq, hxval, hxval', hnum]
  have hres := congrArg (fun z : ZMod (expOrd i) => z.val) (expF_injective hi hf)
  change ((x : ℕ) : ZMod (expOrd i)).val = ((x' : ℕ) : ZMod (expOrd i)).val at hres
  rw [hxval, hxval'] at hres
  exact hdistinct (Prod.ext hres rfl)

/-- A collision between distinct bounded exponent/selector pairs reveals the
challenge exponent: it is `(x' + (m - x)) mod m` when the first selector is true,
and `(x + (m - x')) mod m` otherwise [PS10, proof of Theorem 142.3].

**Proof sketch.** Equal selectors are impossible by cancellation. In the two remaining
cases the collision reads either `g^z g^x = g^x'` or `g^z g^x' = g^x`. The order of
the generator turns each equality into a congruence, and adding the complement of
the second exponent recovers the unique challenge residue below the order. -/
theorem unitCollision_extract {i : List Bool} (hi : ExpValid i)
    {x x' : ℕ} (hx : x < dlM i) (hx' : x' < dlM i)
    (z : ZMod (expOrd i)) {b b' : Bool}
    (hdistinct : (x, b) ≠ (x', b'))
    (hcollision :
      (if b then expUnit hi ^ z.val else 1) * expUnit hi ^ x =
      (if b' then expUnit hi ^ z.val else 1) * expUnit hi ^ x') :
    b ≠ b' ∧ z.val =
      if b then (x' + (dlM i - x)) % dlM i else (x + (dlM i - x')) % dlM i := by
  have hne := unitCollision_selector_ne hi hx hx' z hdistinct hcollision
  refine ⟨hne, ?_⟩
  have hz : z.val < dlM i := lt_of_lt_of_eq (ZMod.val_lt z) (expOrd_of_valid hi)
  cases b <;> cases b'
  · exact (hne rfl).elim
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hcollision ⊢
    exact residue_of_unit_pow_mul hi hz hx' hcollision.symm
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hcollision ⊢
    exact residue_of_unit_pow_mul hi hz hx hcollision
  · exact (hne rfl).elim

end TCSlib.Cryptography.Authentication.FromDiscreteLog
