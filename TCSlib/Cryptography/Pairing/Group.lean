/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Cryptography.Foundations.Probability
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Symmetric bilinear groups and their generators

A *bilinear group* [BB04, §2.2] is a pair of cyclic groups `G`, `G_1` of prime order `p` with a
map `e : G × G → G_1` that is bilinear (`e(u^a, v^b) = e(u, v)^{ab}`) and non-degenerate
(`e(g, g) ≠ 1` for a generator `g`). The pairing is symmetric: `e(u, v) = e(v, u)`. Here the
groups stay abstract. No elliptic curve or concrete pairing (Weil, Tate) is formalized.

**Representation.** A bilinear group is a bundle `BilinearGroup wG wT`: two finite commutative
groups `G` and `GT` (the paper's `G_1`) of the same prime order, a distinguished generator `gen`,
the pairing as a bimultiplicative map `G →* G →* GT`, and injective fixed-width encodings of the
elements of both groups as `wG`- and `wT`-bit strings. A bimultiplicative map is the
multiplicative form of [BB04, §2.2, item 1]: `bilinear_pow` derives `e(u^a, v^b) = e(u, v)^{ab}`.

**The generator.** The asymptotic layer quantifies over non-uniform PPT adversaries
(`Complexity.NUPPT`) and draws the group from a *bilinear group generator*, as the
discrete-logarithm and DDH layers draw theirs from an instance generator
(`Candidates.ExpGroupGen`, `Candidates.SafePrimeGen`). A `BilinearGen` is a PPT `Gen(1^κ)`
whose output string, the *description* `d`, has a fixed polynomial length. The group it describes
is `group κ d`, a total function of the description. So every string describes some bilinear
group, and no validity predicate is needed. Adversaries receive the description.

**Deviation:** [BB04] is concrete (a fixed group `G`, `(t, ε)` bounds); here the group is drawn
by a PPT generator at each security parameter, and security is asymptotic. The efficiency of the
group operations and of the pairing ("efficiently computable", [BB04, §2.2]) is not a field of
the bundle. It is the separate contract `BilinearGen.Ops` (`Pairing/Operations.lean`), assumed
only by the results whose reductions compute in the group.

## Main definitions

* `TCSlib.Cryptography.Pairing.BilinearGroup` — a symmetric bilinear group of prime order with
  fixed-width encodings [BB04, §2.2].
* `TCSlib.Cryptography.Pairing.BilinearGen` — a bilinear group generator; `BilinearGen.desc`,
  `BilinearGen.inst` — the description and the group at the generator's coins;
  `BilinearGen.OrderAtLeastExcept` — the order is large except on a set of coins of small
  probability.

## Main results

* `BilinearGroup.bilinear_pow`, `pair_pow_left`, `pair_pow_right` — bilinearity
  [BB04, §2.2, item 1].
* `BilinearGroup.pair_comm` — the pairing is symmetric [BB04, §2.2, the remark after item 2].
* `BilinearGroup.pow_order`, `BilinearGroup.pow_val_mul` — exponents act through `Z_p`.
* `BilinearGroup.exists_pow_eq` — every element of `G^*` generates `G`.
* `BilinearGroup.pair_ne_one` — every element of `G^*` pairs non-trivially with itself.
* `BilinearGroup.pow_val_bijective` — `a ↦ e(g, g)^a` is a bijection `Z_p → G_1` for `g ∈ G^*`.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §2.2 (bilinear groups).
* [Jou00] A. Joux, *A One Round Protocol for Tripartite Diffie–Hellman*, ANTS-IV, LNCS 1838,
  pp. 385–393, Springer, 2000. §2 (the Weil and Tate pairings are bilinear and non-degenerate).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 26.8, non-uniform PPT; the instance-generator convention of §2.8 and §3.11.)
-/

namespace TCSlib.Cryptography.Pairing

open Complexity

/-- A **symmetric bilinear group of prime order** with fixed-width encodings [BB04, §2.2]: finite
commutative groups `G` and `G_T` (the paper's `G_1`) of the same prime order `p`, a generator `g`
of `G` (`g ≠ 1`; `G` has prime order), a pairing `e : G × G → G_T` that is multiplicative in each
argument, and non-degenerate, `e(g, g) ≠ 1` [BB04, §2.2, items 1–2]. Elements are written as
`wG`-bit (resp. `wT`-bit) strings by injective encodings, the representation handed to machines.

**Deviation:** bilinearity is stated as a bimultiplicative map `G →* G →* G_T`; the paper's
`e(u^a, v^b) = e(u, v)^{ab}` for `a, b ∈ ℤ` is derived (`bilinear_pow`). The fixed generator `gen`
witnesses that `G^* = G ∖ {1}` is not empty; the schemes and assumptions sample their generator
uniformly from `G^*`, as [BB04, §3.1 and §4.1] do. -/
structure BilinearGroup (wG wT : ℕ) where
  /-- The source group `G`. -/
  G : Type
  /-- The target group `G_T` (the paper's `G_1`). -/
  GT : Type
  /-- `G` is a commutative group. -/
  [commGroupG : CommGroup G]
  /-- `G_T` is a commutative group. -/
  [commGroupGT : CommGroup GT]
  /-- `G` is finite. -/
  [fintypeG : Fintype G]
  /-- `G_T` is finite. -/
  [fintypeGT : Fintype GT]
  /-- Equality in `G` is decidable. -/
  [decEqG : DecidableEq G]
  /-- Equality in `G_T` is decidable. -/
  [decEqGT : DecidableEq GT]
  /-- The common prime order `p`. -/
  order : ℕ
  /-- `p` is prime. -/
  order_prime : order.Prime
  /-- `|G| = p`. -/
  card_G : Fintype.card G = order
  /-- `|G_T| = p`. -/
  card_GT : Fintype.card GT = order
  /-- A generator `g` of `G`. -/
  gen : G
  /-- `g ≠ 1`, so `g` generates the group `G` of prime order. -/
  gen_ne_one : gen ≠ 1
  /-- The pairing `e`, multiplicative in each argument. -/
  pair : G →* G →* GT
  /-- Non-degeneracy: `e(g, g) ≠ 1` [BB04, §2.2, item 2]. -/
  pair_gen_ne_one : pair gen gen ≠ 1
  /-- The encoding of `G` as `wG`-bit strings. -/
  encG : G → Fin wG → Bool
  /-- Distinct elements of `G` have distinct encodings. -/
  encG_injective : Function.Injective encG
  /-- The encoding of `G_T` as `wT`-bit strings. -/
  encT : GT → Fin wT → Bool
  /-- Distinct elements of `G_T` have distinct encodings. -/
  encT_injective : Function.Injective encT

attribute [instance] BilinearGroup.commGroupG BilinearGroup.commGroupGT BilinearGroup.fintypeG
  BilinearGroup.fintypeGT BilinearGroup.decEqG BilinearGroup.decEqGT

namespace BilinearGroup

variable {wG wT : ℕ} (B : BilinearGroup wG wT)

/-- The order of a bilinear group is prime, as a `Fact` (so `ZMod B.order` is a field). -/
instance factPrime : Fact B.order.Prime := ⟨B.order_prime⟩

/-- The order of a bilinear group is nonzero (so `ZMod B.order` is finite). -/
instance neZeroOrder : NeZero B.order := ⟨B.order_prime.ne_zero⟩

/-- `G^* = G ∖ {1}` is not empty: it contains the generator `gen`. -/
instance nonempty_ne_one : Nonempty {x : B.G // x ≠ 1} := ⟨⟨B.gen, B.gen_ne_one⟩⟩

/-- **Bilinearity** [BB04, §2.2, item 1]: `e(u^a, v^b) = e(u, v)^{ab}` for natural exponents. -/
theorem bilinear_pow (u v : B.G) (a b : ℕ) : B.pair (u ^ a) (v ^ b) = B.pair u v ^ (a * b) := by
  rw [map_pow (B.pair (u ^ a)) v b, map_pow B.pair u a, MonoidHom.pow_apply, ← pow_mul,
    mul_comm]

/-- Bilinearity in the first argument: `e(u^a, v) = e(u, v)^a`. -/
theorem pair_pow_left (u v : B.G) (a : ℕ) : B.pair (u ^ a) v = B.pair u v ^ a := by
  rw [map_pow, MonoidHom.pow_apply]

/-- Bilinearity in the second argument: `e(u, v^b) = e(u, v)^b`. -/
theorem pair_pow_right (u v : B.G) (b : ℕ) : B.pair u (v ^ b) = B.pair u v ^ b :=
  map_pow (B.pair u) v b

/-- `|G| = p` as a `Nat.card`: `Nat.card B.G = B.order`. -/
theorem natCard_G : Nat.card B.G = B.order := by
  rw [Nat.card_eq_fintype_card, B.card_G]

/-- **Every element of `G^*` generates `G`**: for `g ≠ 1` and any `x`, `x = g^n` for some `n`
(`G` has prime order). -/
theorem exists_pow_eq {g : B.G} (hg : g ≠ 1) (x : B.G) : ∃ n : ℕ, g ^ n = x :=
  (Submonoid.mem_powers_iff _ _).1 (mem_powers_of_prime_card B.natCard_G hg)

/-- **The pairing is symmetric** [BB04, §2.2, the remark after item 2]: `e(u, v) = e(v, u)`,
since `e(g^a, g^b) = e(g, g)^{ab} = e(g^b, g^a)`. -/
theorem pair_comm (u v : B.G) : B.pair u v = B.pair v u := by
  obtain ⟨a, rfl⟩ := B.exists_pow_eq B.gen_ne_one u
  obtain ⟨b, rfl⟩ := B.exists_pow_eq B.gen_ne_one v
  rw [B.bilinear_pow, B.bilinear_pow, mul_comm]

/-- `x^p = 1` in `G`: Lagrange's theorem with `|G| = p`. -/
theorem pow_order (x : B.G) : x ^ B.order = 1 := by
  rw [← B.card_G]
  exact pow_card_eq_one

/-- `y^p = 1` in `G_T`: Lagrange's theorem with `|G_T| = p`. -/
theorem pow_order_GT (y : B.GT) : y ^ B.order = 1 := by
  rw [← B.card_GT]
  exact pow_card_eq_one

/-- Exponents of `G` act through `Z_p`: `x^{(ab mod p)} = (x^a)^b` read in `Z_p`, i.e.
`x ^ (a * b).val = x ^ (a.val * b.val)` for `a, b ∈ Z_p`. -/
theorem pow_val_mul (x : B.G) (a b : ZMod B.order) : x ^ (a * b).val = x ^ (a.val * b.val) := by
  rw [ZMod.val_mul, ← Nat.mod_add_div (a.val * b.val) B.order, pow_add, pow_mul, B.pow_order,
    one_pow, mul_one, Nat.mod_add_div]

/-- Exponents of `G_T` act through `Z_p`: `y ^ (a * b).val = y ^ (a.val * b.val)`. -/
theorem pow_val_mul_GT (y : B.GT) (a b : ZMod B.order) :
    y ^ (a * b).val = y ^ (a.val * b.val) := by
  rw [ZMod.val_mul, ← Nat.mod_add_div (a.val * b.val) B.order, pow_add, pow_mul, B.pow_order_GT,
    one_pow, mul_one, Nat.mod_add_div]

/-- **Non-degeneracy at every generator**: `e(x, x) ≠ 1` for every `x ∈ G^*` (from
`e(g, g) ≠ 1` [BB04, §2.2, item 2], since every `x ∈ G^*` generates `G`).

**Proof sketch.** Write `x = g^k` with `k ≢ 0 (mod p)` (`x ≠ 1`). Then
`e(x, x) = e(g, g)^{k²}` by bilinearity. The element `e(g, g) ≠ 1` of the group `G_T` of prime
order `p` has order `p`, and `p ∤ k²` because `p` is prime and `p ∤ k`. -/
theorem pair_ne_one {x : B.G} (hx : x ≠ 1) : B.pair x x ≠ 1 := by
  obtain ⟨k, rfl⟩ := B.exists_pow_eq B.gen_ne_one x
  rw [B.bilinear_pow]
  intro h
  have ho : orderOf (B.pair B.gen B.gen) = B.order :=
    orderOf_eq_prime (B.pow_order_GT _) B.pair_gen_ne_one
  have hd : B.order ∣ k * k := ho ▸ orderOf_dvd_of_pow_eq_one h
  obtain ⟨j, rfl⟩ : B.order ∣ k := ((Nat.Prime.dvd_mul B.order_prime).1 hd).elim id id
  exact hx (by rw [pow_mul, B.pow_order, one_pow])

/-- **`a ↦ e(x, x)^a` is a bijection `Z_p → G_T`** for every `x ∈ G^*`: the law of `e(x, x)^z`
for uniform `z ∈ Z_p` is uniform on `G_T` (the identification of [BB04, §3.1]'s "`T` uniform in
`G_1`" with `e(g, g)^z`, `z` uniform, used by the proofs).

**Proof sketch.** `e(x, x) ≠ 1` (`pair_ne_one`) has prime order `p` in `G_T`, so
`a ↦ e(x, x)^{a.val}` is injective on `Z_p`; both sides have `p` elements (`card_GT`). -/
theorem pow_val_bijective {x : B.G} (hx : x ≠ 1) :
    Function.Bijective fun a : ZMod B.order => B.pair x x ^ a.val := by
  have ho : orderOf (B.pair x x) = B.order :=
    orderOf_eq_prime (B.pow_order_GT _) (B.pair_ne_one hx)
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun a b hab => ZMod.val_injective _ ?_, by rw [ZMod.card, B.card_GT]⟩
  have h := pow_eq_pow_iff_modEq.1 hab
  rw [ho] at h
  exact Nat.ModEq.eq_of_lt_of_lt h (ZMod.val_lt a) (ZMod.val_lt b)

end BilinearGroup

/-- A **bilinear group generator**: a PPT `Gen(1^κ)` whose output, the *description* `d` of the
group, has `descLen(κ)` bits, and the bilinear group `group κ d` that `d` describes, with element
widths `wG(κ)` and `wT(κ)`. The form of [BB04, §2.2] ("`G` is a bilinear group") and of
[BB04, §4.1] ("the security parameter determines the size of `G`") in the asymptotic layer.

**Deviation:** the group is a total function of the description (every string describes some
bilinear group), so no validity predicate or threshold appears, unlike `Candidates.ExpGroupGen`;
descriptions have an exact polynomial length (a PPT generator can always pad its output to its
time bound). The order of the group is unconstrained here: results that need a large order
assume `OrderAtLeastExcept`. Efficient group operations are the separate contract
`BilinearGen.Ops`. -/
structure BilinearGen where
  /-- The generator `Gen(1^κ)`, run on the empty argument. -/
  gen : NUPPT
  /-- `Gen` is a PPT. -/
  gen_uniform : gen.Uniform
  /-- The length of a description. -/
  descLen : PolyExpr
  /-- Every description at parameter `κ` has `descLen(κ)` bits. -/
  desc_length : ∀ κ (r : gen.Coins κ), (gen.runAt κ [] r).length = descLen.eval κ
  /-- The width of the encoding of `G`. -/
  wG : PolyExpr
  /-- The width of the encoding of `G_T`. -/
  wT : PolyExpr
  /-- The bilinear group described by a string at parameter `κ`. -/
  group : (κ : ℕ) → List Bool → BilinearGroup (wG.eval κ) (wT.eval κ)

namespace BilinearGen

variable (G : BilinearGen)

/-- The description `d = Gen(1^κ; r)` output by the generator on the coins `r`. -/
def desc (κ : ℕ) (r : G.gen.Coins κ) : List Bool := G.gen.runAt κ [] r

/-- `G.desc κ r = G.gen.runAt κ [] r`. -/
theorem desc_eq (κ : ℕ) (r : G.gen.Coins κ) : G.desc κ r = G.gen.runAt κ [] r := rfl

/-- A description has `descLen(κ)` bits: `(G.desc κ r).length = G.descLen.eval κ`. -/
theorem length_desc (κ : ℕ) (r : G.gen.Coins κ) : (G.desc κ r).length = G.descLen.eval κ :=
  G.desc_length κ r

/-- The bilinear group generated on the coins `r`: `G.inst κ r = G.group κ (G.desc κ r)`. -/
def inst (κ : ℕ) (r : G.gen.Coins κ) : BilinearGroup (G.wG.eval κ) (G.wT.eval κ) :=
  G.group κ (G.desc κ r)

/-- `G.inst κ r = G.group κ (G.desc κ r)`. -/
theorem inst_eq (κ : ℕ) (r : G.gen.Coins κ) : G.inst κ r = G.group κ (G.desc κ r) := rfl

/-- **The order is at least `N(κ)` except with probability `δ(κ)`**: for every `κ`,
`Pr_r[|G| < N(κ)] ≤ δ(κ)` over the generator's coins `r`. With `N(κ) = 2^κ` and a negligible
`δ` this is "the security parameter determines the size of `G`" [BB04, §4.1]; with
`N(κ) = 2^{ℓ(κ)}` it makes `ℓ(κ)`-bit identities distinct in `Z_p` [BB04, §4.4, "`2^b < p`"].

**Deviation:** a strict PPT generator may fail with small probability, so a bound on every coin
string is not demanded (the lesson of `Candidates.ExpGroupGen.FullLengthExcept`, run-3 audit
P8-2). -/
def OrderAtLeastExcept (N : ℕ → ℕ) (δ : ℕ → ℝ) : Prop :=
  ∀ κ, uprob (fun r : G.gen.Coins κ => (G.inst κ r).order < N κ) ≤ δ κ

/-- `G.OrderAtLeastExcept N δ` iff for every `κ` the probability over the generator's coins that
the order is below `N κ` is at most `δ κ`. -/
theorem orderAtLeastExcept_iff (N : ℕ → ℕ) (δ : ℕ → ℝ) :
    G.OrderAtLeastExcept N δ ↔
      ∀ κ, uprob (fun r : G.gen.Coins κ => (G.inst κ r).order < N κ) ≤ δ κ :=
  Iff.rfl

end BilinearGen

end TCSlib.Cryptography.Pairing
