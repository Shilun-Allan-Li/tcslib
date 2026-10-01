/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.DeterministicCC.DetBasic
import TCSlib.CommunicationComplexity.DeterministicCC.UpperBounds
import TCSlib.CommunicationComplexity.DeterministicCC.Rectangle
import TCSlib.CommunicationComplexity.DeterministicCC.DetRectangle
import TCSlib.CommunicationComplexity.DeterministicCC.Helper
import TCSlib.CommunicationComplexity.NewmanTheorem.FuncHash
import TCSlib.CommunicationComplexity.NewmanTheorem.PublicCoinComplexity

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Equality Function Communication Complexity

The equality function `EQ_n` on `n`-bit strings [RY20, Ch. 1, eq. (1.1)] and its
communication complexity: the trivial `(n + 1)`-bit deterministic protocol, the matching
lower bound `D(EQ_n) ≥ n + 1` obtained by counting monochromatic rectangles
[RY20, Thm 1.14], and the public-coin hashing protocol of [RY20, Ch. 3, Figure 3.1], which
gives `R^pub_ε(EQ_n) ≤ ⌈log₂(⌈ε⁻¹⌉ + 1)⌉ + 1`.

## Main definitions

- `Functions.Equality.equality`: the equality function on `n`-bit strings.
- `Functions.Equality.HashSpace`: the public randomness of the hashing protocol, a uniformly
  random function from `n`-bit strings to `Fin (2 ^ k)`.
- `Functions.Equality.equalityHashProtocol`: the public-coin hashing protocol for equality.

## Main results

- `Functions.Equality.communicationComplexity_eq`: the exact deterministic communication
  complexity of equality on `n`-bit strings is `0` when `n = 0` and `n + 1` otherwise.
- `Functions.Equality.publicCoin_communicationComplexity_le`: the public-coin communication
  complexity of equality at any error `ε > 0` is at most `Nat.clog 2 (⌈ε⁻¹⌉₊ + 1) + 1`.

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [Rou16] T. Roughgarden, *Communication Complexity (for Algorithm Designers)*,
  Foundations and Trends in Theoretical Computer Science 11(3–4), 2016; arXiv:1509.06257.
* [Yao79] A. C.-C. Yao, "Some complexity questions related to distributive computing",
  *STOC 1979*, pp. 209–213.
* [KN97] E. Kushilevitz, N. Nisan, *Communication Complexity*, Cambridge University
  Press, 1997.

Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal.
-/

namespace CommunicationComplexity

open MeasureTheory

namespace Functions.Equality

/-- The equality function on `n`-bit strings: `equality n x y` is `true` if and only if
`x = y` [RY20, Ch. 1, eq. (1.1)]. -/
def equality (n : ℕ) (x y : BoolInput n) : Bool :=
  decide (x = y)

/-- The public randomness for the hashing protocol: a uniformly random
hash function from `n`-bit strings into `Fin (2 ^ k)`. -/
abbrev HashSpace (n k : ℕ) := Functions.Hash.HashSpace (BoolInput n) (2 ^ k)

instance hashRangeNeZero (k : ℕ) : NeZero (2 ^ k) := ⟨pow_ne_zero _ (by decide)⟩

/-- `Nat.clog 2 2 = 1`, kernel-checked (replaces a former `native_decide`). -/
private theorem clog_two_two : Nat.clog 2 2 = 1 := Nat.clog_eq_one le_rfl le_rfl

/-- The deterministic communication complexity of equality on `n`-bit strings is at most
`n + 1`: Alice sends her `n`-bit input, Bob computes equality and sends one bit
[RY20, Ch. 1, §Equality: 'Alice sending her input yields an (n+1)-bit protocol']. -/
theorem communicationComplexity_le (n : ℕ) :
    Deterministic.communicationComplexity (equality n) ≤ n + 1 := by
  calc Deterministic.communicationComplexity (equality n)
      ≤ Nat.clog 2 (Nat.card (Fin n → Bool)) + Nat.clog 2 (Nat.card Bool) :=
        Deterministic.communicationComplexity_le_clog_card_X_alpha (equality n)
    _ = n + 1 := by
        simp only [Nat.card_eq_fintype_card, Fintype.card_pi, Fintype.card_bool,
          Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.one_lt_ofNat,
          Nat.clog_pow, clog_two_two]
        norm_cast

/-- When n = 0, equality has communication complexity 0: both inputs are
the unique empty function, so the output is always `true`. -/
theorem communicationComplexity_zero :
    Deterministic.communicationComplexity (equality 0) = 0 := by
  apply le_antisymm
  · change Deterministic.communicationComplexity (equality 0) ≤ (0 : ℕ)
    rw [Deterministic.communicationComplexity_le_iff]
    exact ⟨Deterministic.Protocol.output true, by
      ext x y; simp [equality, Deterministic.Protocol.run, Subsingleton.elim x y],
      by simp [Deterministic.Protocol.complexity]⟩
  · exact bot_le

open Deterministic.Protocol Rectangle in
/-- For `n ≥ 1`, the deterministic communication complexity of equality on `n`-bit strings
is at least `n + 1` [RY20, Thm 1.14], via [RY20, Claim 1.13]: any monochromatic rectangle
containing a diagonal point `(x, x)` contains no other diagonal point, so every
monochromatic partition has at least `2 ^ n + 1` parts, which requires `n + 1` bits.

**Proof sketch.** By the rectangle lower bound
(`Deterministic.le_communicationComplexity_of_forall_lt_ncard`) it suffices to show that
every monochromatic rectangle partition of the input space has more than `2 ^ n` parts.
Step 1: for each string `x` choose a part `rect x` containing the diagonal point `(x, x)`.
Step 2: `rect` is injective. If `rect x = rect y` with `x ≠ y`, then `(x, y)` lies in the
same rectangle by the cross-membership property of rectangles, and monochromaticity forces
`EQ(x, y) = EQ(x, x) = true`, contradicting `x ≠ y` (this is [RY20, Claim 1.13]).
Step 3: hence the range of `rect` has exactly `2 ^ n` elements. Step 4: the part `R0`
containing the off-diagonal point `(1ⁿ, 0ⁿ)` (which exists since `n ≥ 1`) is
`false`-monochromatic, so it is not in the range of `rect`. Step 5: adjoining `R0` to the
range of `rect` gives a subset of the partition with `2 ^ n + 1` parts. -/
theorem le_communicationComplexity (n : ℕ) (hn : 1 ≤ n) :
    (n + 1 : ℕ) ≤ Deterministic.communicationComplexity (equality n) := by
  apply Deterministic.le_communicationComplexity_of_forall_lt_ncard
  intro Part hPart
  -- Step 1: each (x,x) is in some rectangle in Part
  choose rect hrect_mem hrect_in using fun x =>
    monoPartition_point_mem hPart (x, x)
  -- Step 2: rect is injective: if rect x = rect y, then (x,x) and (y,y)
  -- are in the same rectangle, so (x,y) is too (cross_mem),
  -- and mono gives equality x x = equality x y, forcing x = y.
  have hrect_inj : Function.Injective rect := by
    intro x y hxy
    by_contra hne
    have hxy_mem := (monoPartition_cross_mem hPart (hrect_mem x)
      (hrect_in x) (hxy ▸ hrect_in y)).2
    have := monoPartition_values_eq hPart (hrect_mem x) (hrect_in x) hxy_mem
    simp [equality, hne] at this
  -- Step 3: the image of rect has size 2^n
  have himage_card :
      Set.ncard (Set.range rect) = 2 ^ n := by
    simpa [Fintype.card_bool, Fintype.card_fin] using
      Set.ncard_range_of_injective hrect_inj
  -- Step 4: find a "false" rectangle containing (x0, y0) with x0 ≠ y0
  have hx : (fun _ : Fin n => true) ≠ (fun _ : Fin n => false) := by
    intro h; have := congr_fun h ⟨0, hn⟩; simp at this
  set x0 : BoolInput n := fun _ => true
  set y0 : BoolInput n := fun _ => false
  obtain ⟨R0, hR0_mem, hR0_in⟩ := monoPartition_point_mem hPart (x0, y0)
  -- R0 is not in the image of rect: any rect z is "true"-mono,
  -- but R0 contains (x0, y0) with equality x0 y0 = false.
  have hR0_not_diag : R0 ∉ Set.range rect := by
    rintro ⟨z, rfl⟩
    have := monoPartition_values_eq hPart (hrect_mem z) (hrect_in z) hR0_in
    simp [equality, hx] at this
  -- Step 5: insert R0 into range rect ⊆ Part, giving 2^n < |Part|
  have hinsert : insert R0 (Set.range rect) ⊆ Part :=
    Set.insert_subset hR0_mem (fun R ⟨x, hx⟩ => hx ▸ hrect_mem x)
  calc 2 ^ n
      = Set.ncard (Set.range rect) := himage_card.symm
    _ < Set.ncard (insert R0 (Set.range rect)) := by
        rw [Set.ncard_insert_of_notMem hR0_not_diag, himage_card]; omega
    _ ≤ Set.ncard Part :=
        Set.ncard_le_ncard hinsert (Set.toFinite Part)

/-- The exact deterministic communication complexity of equality on `n`-bit strings is
`0` when `n = 0` and `n + 1` otherwise; the lower bound is [RY20, Thm 1.14] and the upper
bound is the trivial protocol. Deviation: [RY20] only states the lower bound `≥ n + 1`;
here the exact value is given, including the degenerate case `n = 0`. -/
theorem communicationComplexity_eq (n : ℕ) :
    Deterministic.communicationComplexity (equality n) =
      if n = 0 then 0 else n + 1 := by
  split
  · next h => subst h; exact communicationComplexity_zero
  · next h =>
    apply le_antisymm (communicationComplexity_le n)
    exact le_communicationComplexity n (by omega)

/-- The standard public-coin equality protocol from a shared random hash function
`h : {0,1}^n → Fin (2 ^ k)` [RY20, Ch. 3, Public-coin protocol (Figure 3.1)]: Alice sends
`h x`, Bob compares it with `h y` and sends the comparison bit, which is the output. -/
noncomputable def equalityHashProtocol (n k : ℕ) :
    PublicCoin.FiniteMessage.Protocol (HashSpace n k) (BoolInput n) (BoolInput n) Bool :=
  PublicCoin.FiniteMessage.Protocol.alice
    (fun x h => h x)
    (fun hx =>
      PublicCoin.FiniteMessage.Protocol.bob
        (fun y h => decide (h y = hx))
        (fun b => PublicCoin.FiniteMessage.Protocol.output b))

/-- On inputs `x`, `y` and shared hash function `h`, the hashing protocol outputs `true` if
and only if `h x = h y`. -/
@[simp] theorem equalityHashProtocol_rrun
    (n k : ℕ) (x y : BoolInput n) (h : HashSpace n k) :
    (equalityHashProtocol n k).rrun x y h = decide (h x = h y) := by
  change decide (h y = h x) = decide (h x = h y)
  simp [eq_comm]

/-- The hashing protocol with hash range `Fin (2 ^ k)` communicates exactly `k + 1` bits:
`k` for Alice's hash value and one for Bob's comparison bit. -/
@[simp] theorem equalityHashProtocol_complexity
    (n k : ℕ) :
    (equalityHashProtocol n k).complexity = k + 1 := by
  unfold equalityHashProtocol PublicCoin.FiniteMessage.Protocol.alice
    PublicCoin.FiniteMessage.Protocol.bob PublicCoin.FiniteMessage.Protocol.output
  simp only [Deterministic.FiniteMessage.Protocol.complexity,
    Fintype.card_fin, Fintype.univ_bool, Finset.sup_insert,
    Finset.sup_singleton]
  rw [show Nat.clog 2 (2 ^ k) = k by
    exact Nat.clog_pow 2 k (by decide)]
  have hbool : Nat.clog 2 (Fintype.card Bool) + max 0 0 = 1 := by
    simp [Fintype.card_bool, clog_two_two]
  simp only [hbool]
  rw [Finset.sup_const Finset.univ_nonempty 1]

/-- If the hash range has size `2 ^ k` and `1 / 2 ^ k < ε`, then the public-coin
communication complexity of equality on `n`-bit strings at worst-case error `ε` is at most
`k + 1` [RY20, Ch. 3, Public-coin protocol (Figure 3.1)]. Deviation: [RY20] states the
collision probability `≤ 2^{-k}` and calls the communication "a constant number of bits";
here the hash range is `Fin (2 ^ k)`, the error threshold `ε` is explicit, and the bit
count `k + 1` is exact.

**Proof sketch.** Step 1: the public-coin complexity is bounded by the complexity of any
finite-message protocol whose worst-case error is at most some `δ < ε`
(`PublicCoin.communicationComplexity_le_of_finiteMessage`), applied to the hashing
protocol with `δ = 1 / 2 ^ k`; it remains to bound the error input by input. Step 2: on
equal inputs `x = y` the protocol never errs, since `h x = h x`. Step 3: on distinct
inputs the error event is exactly the collision event `h x = h y`, whose probability under a
uniformly random `h` is at most `1 / 2 ^ k` (`Functions.Hash.collision_prob_le`). Step 4:
the hashing protocol has complexity `k + 1` (`equalityHashProtocol_complexity`). -/
theorem publicCoin_communicationComplexity_le_of_hε
    (n k : ℕ) {ε : ℝ} (hε : (1 : ℝ) / 2 ^ k < ε) :
    PublicCoin.communicationComplexity (equality n) ε ≤ k + 1 := by
  -- Step 1: we use the random-hash protocol over the finite probability space
  -- of all functions `BoolInput n → Fin (2 ^ k)`.
  have hcc :
      PublicCoin.communicationComplexity (equality n) ε ≤
        (equalityHashProtocol n k).complexity := by
    refine PublicCoin.communicationComplexity_le_of_finiteMessage
      (f := equality n) ε ((1 : ℝ) / 2 ^ k) hε (equalityHashProtocol n k) ?_
    -- We now verify the worst-case error bound input by input.
    intro x y
    by_cases hxy : x = y
    · -- Step 2: on equal inputs, Bob always receives the same hash value as Alice.
      subst hxy
      have hset :
          {ω : HashSpace n k | (equalityHashProtocol n k).rrun x x ω ≠ equality n x x} = ∅ := by
        ext ω
        change (decide (ω x = ω x) ≠ decide (x = x)) ↔ False
        simp
      rw [hset]
      simp
    · -- Step 3: on distinct inputs, the protocol errs exactly on a hash collision.
      have hset :
          {ω : HashSpace n k |
            (equalityHashProtocol n k).rrun x y ω ≠ equality n x y} =
          {ω : HashSpace n k | ω x = ω y} := by
        ext ω
        simpa [Set.mem_setOf_eq] using
          (show ((equalityHashProtocol n k).rrun x y ω ≠ equality n x y) ↔ ω x = ω y from by
            rw [equalityHashProtocol_rrun]
            simp [equality, hxy, eq_comm])
      rw [hset]
      simpa using Functions.Hash.collision_prob_le (α := BoolInput n) (2 ^ k) x y hxy
  -- Step 4: the hashing protocol has complexity `k + 1`.
  simpa [equalityHashProtocol_complexity] using hcc

/-- For every error `ε > 0`, the public-coin communication complexity of equality on
`n`-bit strings at worst-case error `ε` is at most `⌈log₂(⌈ε⁻¹⌉ + 1)⌉ + 1`
[RY20, Ch. 3, Public-coin protocol (Figure 3.1)]. Deviation: this makes the "constant
number of bits" of [RY20] an explicit function of `ε`, obtained by choosing the hash range
`Fin (2 ^ k)` with `k = ⌈log₂(⌈ε⁻¹⌉ + 1)⌉`.

**Proof sketch.** Let `k = ⌈log₂(⌈ε⁻¹⌉ + 1)⌉`. Step 1: `ε⁻¹ < ⌈ε⁻¹⌉ + 1`. Step 2:
`⌈ε⁻¹⌉ + 1 ≤ 2 ^ k` by the defining property of the ceiling logarithm. Step 3: combining,
`ε⁻¹ < 2 ^ k` as real numbers, hence `1 / 2 ^ k < ε`. Step 4: apply
`publicCoin_communicationComplexity_le_of_hε` with this `k`. -/
theorem publicCoin_communicationComplexity_le
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    PublicCoin.communicationComplexity (equality n) ε ≤
      Nat.clog 2 (⌈ε⁻¹⌉₊ + 1) + 1 := by
  let k := Nat.clog 2 (⌈ε⁻¹⌉₊ + 1)
  -- Step 1: `ε⁻¹ < ⌈ε⁻¹⌉ + 1`
  have hεinv_lt : ε⁻¹ < ((⌈ε⁻¹⌉₊ + 1 : ℕ) : ℝ) := by
    calc
      ε⁻¹ ≤ ((⌈ε⁻¹⌉₊ : ℕ) : ℝ) := Nat.le_ceil (ε⁻¹)
      _ < ((⌈ε⁻¹⌉₊ : ℕ) : ℝ) + 1 := by norm_num
      _ = ((⌈ε⁻¹⌉₊ + 1 : ℕ) : ℝ) := by norm_num
  -- Step 2: `⌈ε⁻¹⌉ + 1 ≤ 2 ^ k`
  have hk_nat : ⌈ε⁻¹⌉₊ + 1 ≤ 2 ^ k := by
    dsimp [k]
    exact Nat.le_pow_clog (by decide) (⌈ε⁻¹⌉₊ + 1)
  -- Step 3: `ε⁻¹ < 2 ^ k` over `ℝ`, hence `1 / 2 ^ k < ε`
  have hk_real : ε⁻¹ < (2 ^ k : ℝ) := by
    have hk_nat' : (((⌈ε⁻¹⌉₊ + 1 : ℕ) : ℝ)) ≤ (((2 ^ k : ℕ) : ℝ)) := by
      exact_mod_cast hk_nat
    calc
      ε⁻¹ < (((⌈ε⁻¹⌉₊ + 1 : ℕ) : ℝ)) := hεinv_lt
      _ ≤ (((2 ^ k : ℕ) : ℝ)) := hk_nat'
      _ = (2 ^ k : ℝ) := by norm_num
  have hk_pos : (0 : ℝ) < 2 ^ k := by positivity
  have hbound : (1 : ℝ) / 2 ^ k < ε := by
    rw [div_lt_iff₀ hk_pos]
    have hmul := mul_lt_mul_of_pos_left hk_real hε
    simpa [hε.ne'] using hmul
  -- Step 4: apply the fixed-`k` bound
  simpa [k] using publicCoin_communicationComplexity_le_of_hε n k hbound

end Functions.Equality

end CommunicationComplexity
