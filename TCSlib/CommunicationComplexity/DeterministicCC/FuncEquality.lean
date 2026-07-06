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

## Main results

- `Functions.Equality.communicationComplexity_eq`: The exact deterministic communication complexity of equality on `n`-bit strings is `0` when `n = 0` and `n + 1` otherwise.
- `Functions.Equality.publicCoin_communicationComplexity_le`: Public-coin communication complexity of equality is at most `Nat.clog 2 (⌈ε⁻¹⌉₊ + 1) + 1` for any `ε > 0`.

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

namespace CommunicationComplexity

open MeasureTheory

namespace Functions.Equality

/-- The equality function on `n`-bit strings. Returns `true` iff the two inputs are equal. -/
def equality (n : ℕ) (x y : BoolInput n) : Bool :=
  decide (x = y)

/-- The public randomness for the hashing protocol: a uniformly random
hash function from `n`-bit strings into `Fin (2 ^ k)`. -/
abbrev HashSpace (n k : ℕ) := Functions.Hash.HashSpace (BoolInput n) (2 ^ k)

instance hashRangeNeZero (k : ℕ) : NeZero (2 ^ k) := ⟨pow_ne_zero _ (by decide)⟩

/-- The deterministic communication complexity of equality is at most n + 1:
Alice sends her n-bit input, Bob computes equality and sends one bit. -/
theorem communicationComplexity_le (n : ℕ) :
    Deterministic.communicationComplexity (equality n) ≤ n + 1 := by
  calc Deterministic.communicationComplexity (equality n)
      ≤ Nat.clog 2 (Nat.card (Fin n → Bool)) + Nat.clog 2 (Nat.card Bool) :=
        Deterministic.communicationComplexity_le_clog_card_X_alpha (equality n)
    _ = n + 1 := by
        simp only [Nat.card_eq_fintype_card, Fintype.card_pi, Fintype.card_bool,
          Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.one_lt_ofNat,
          Nat.clog_pow, show Nat.clog 2 2 = 1 from by native_decide]
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
/-- The deterministic communication complexity of equality on n-bit strings
is at least n + 1 (for n ≥ 1). Any monochromatic rectangle containing
(x, x) must be {(x, x)}, so there are at least 2^n + 1 rectangles
in any partition, which requires n + 1 bits. -/
theorem le_communicationComplexity (n : ℕ) (hn : 1 ≤ n) :
    (n + 1 : ℕ) ≤ Deterministic.communicationComplexity (equality n) := by
  apply Deterministic.le_communicationComplexity_of_forall_lt_ncard
  intro Part hPart
  -- Each (x,x) is in some rectangle in Part
  choose rect hrect_mem hrect_in using fun x =>
    monoPartition_point_mem hPart (x, x)
  -- rect is injective: if rect x = rect y, then (x,x) and (y,y)
  -- are in the same rectangle, so (x,y) is too (cross_mem),
  -- and mono gives equality x x = equality x y, forcing x = y.
  have hrect_inj : Function.Injective rect := by
    intro x y hxy
    by_contra hne
    have hxy_mem := (monoPartition_cross_mem hPart (hrect_mem x)
      (hrect_in x) (hxy ▸ hrect_in y)).2
    have := monoPartition_values_eq hPart (hrect_mem x) (hrect_in x) hxy_mem
    simp [equality, hne] at this
  -- The image of rect has size 2^n
  have himage_card :
      Set.ncard (Set.range rect) = 2 ^ n := by
    simpa [Fintype.card_bool, Fintype.card_fin] using
      Set.ncard_range_of_injective hrect_inj
  -- Find a "false" rectangle containing (x0, y0) with x0 ≠ y0
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
  -- insert R0 into range rect ⊆ Part, giving 2^n < |Part|
  have hinsert : insert R0 (Set.range rect) ⊆ Part :=
    Set.insert_subset hR0_mem (fun R ⟨x, hx⟩ => hx ▸ hrect_mem x)
  calc 2 ^ n
      = Set.ncard (Set.range rect) := himage_card.symm
    _ < Set.ncard (insert R0 (Set.range rect)) := by
        rw [Set.ncard_insert_of_notMem hR0_not_diag, himage_card]; omega
    _ ≤ Set.ncard Part :=
        Set.ncard_le_ncard hinsert (Set.toFinite Part)

/-- The exact deterministic communication complexity of equality on
`n`-bit strings: 0 when `n = 0`, and `n + 1` otherwise. -/
theorem communicationComplexity_eq (n : ℕ) :
    Deterministic.communicationComplexity (equality n) =
      if n = 0 then 0 else n + 1 := by
  split
  · next h => subst h; exact communicationComplexity_zero
  · next h =>
    apply le_antisymm (communicationComplexity_le n)
    exact le_communicationComplexity n (by omega)

/-- The standard public-coin equality protocol from a random hash
function: Alice sends `h x`, Bob compares it with `h y`, and then sends
the comparison bit. -/
noncomputable def equalityHashProtocol (n k : ℕ) :
    PublicCoin.FiniteMessage.Protocol (HashSpace n k) (BoolInput n) (BoolInput n) Bool :=
  PublicCoin.FiniteMessage.Protocol.alice
    (fun x h => h x)
    (fun hx =>
      PublicCoin.FiniteMessage.Protocol.bob
        (fun y h => decide (h y = hx))
        (fun b => PublicCoin.FiniteMessage.Protocol.output b))

@[simp] theorem equalityHashProtocol_rrun
    (n k : ℕ) (x y : BoolInput n) (h : HashSpace n k) :
    (equalityHashProtocol n k).rrun x y h = decide (h x = h y) := by
  change decide (h y = h x) = decide (h x = h y)
  simp [eq_comm]

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
  have hbool : Nat.clog 2 (Fintype.card Bool) + max 0 0 = 1 := by native_decide
  simp only [hbool]
  rw [Finset.sup_const Finset.univ_nonempty 1]

/-- Public-coin upper bound for equality: if the hash range has size
`2 ^ k` and `1 / 2 ^ k < ε`, then the equality protocol has
communication complexity at most `k + 1`. -/
theorem publicCoin_communicationComplexity_le_of_hε
    (n k : ℕ) {ε : ℝ} (hε : (1 : ℝ) / 2 ^ k < ε) :
    PublicCoin.communicationComplexity (equality n) ε ≤ k + 1 := by
  -- We use the random-hash protocol over the finite probability space
  -- of all functions `BoolInput n → Fin (2 ^ k)`.
  have hcc :
      PublicCoin.communicationComplexity (equality n) ε ≤
        (equalityHashProtocol n k).complexity := by
    refine PublicCoin.communicationComplexity_le_of_finiteMessage
      (f := equality n) ε ((1 : ℝ) / 2 ^ k) hε (equalityHashProtocol n k) ?_
    -- We now verify the worst-case error bound input by input.
    intro x y
    by_cases hxy : x = y
    · -- On equal inputs, Bob always receives the same hash value as Alice.
      subst hxy
      have hset :
          {ω : HashSpace n k | (equalityHashProtocol n k).rrun x x ω ≠ equality n x x} = ∅ := by
        ext ω
        change (decide (ω x = ω x) ≠ decide (x = x)) ↔ False
        simp
      rw [hset]
      simp
    · -- On distinct inputs, the protocol errs exactly on a hash collision.
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
  simpa [equalityHashProtocol_complexity] using hcc

/-- Public-coin upper bound for equality as a direct function of `ε`. -/
theorem publicCoin_communicationComplexity_le
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    PublicCoin.communicationComplexity (equality n) ε ≤
      Nat.clog 2 (⌈ε⁻¹⌉₊ + 1) + 1 := by
  let k := Nat.clog 2 (⌈ε⁻¹⌉₊ + 1)
  have hεinv_lt : ε⁻¹ < ((⌈ε⁻¹⌉₊ + 1 : ℕ) : ℝ) := by
    calc
      ε⁻¹ ≤ ((⌈ε⁻¹⌉₊ : ℕ) : ℝ) := Nat.le_ceil (ε⁻¹)
      _ < ((⌈ε⁻¹⌉₊ : ℕ) : ℝ) + 1 := by norm_num
      _ = ((⌈ε⁻¹⌉₊ + 1 : ℕ) : ℝ) := by norm_num
  have hk_nat : ⌈ε⁻¹⌉₊ + 1 ≤ 2 ^ k := by
    dsimp [k]
    exact Nat.le_pow_clog (by decide) (⌈ε⁻¹⌉₊ + 1)
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
  simpa [k] using publicCoin_communicationComplexity_le_of_hε n k hbound

end Functions.Equality

end CommunicationComplexity
