/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.CoinRelabel
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.RelabelGarbling
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.RowFromCoins

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The tape-to-seed coin relabeling bridge

The seed function is a parameter, specified by its key, nonce and shift-bit
readers. Relabeling its complete tape agrees with the generic seed relabeling.
Assignment XOR is extended to four row codes by the existing finite-embedding
permutation extension, which fixes unused codes. Unused key and shift positions
are padded with false masks.

## Main definitions

* `assignmentEmbedding`, `assignmentPerm`: assignment folds and their extended XOR permutation.
* `keyMask`, `rowPerm`, `shiftMask`: the padded coordinate actions on complete tapes.

## Main results

* `seed_relabel`: the seed of the relabeled tape is the relabeling of the original seed.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Protocol 162.6 and Theorem 163.7 (the coin relabeling).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel

open BoolCircuit TCSlib.Cryptography

/-- The binary fold of an assignment to at most two argument positions is below four.
This uses the published first-two-bit formula. [PS10, Protocol 162.6] -/
theorem assignmentFold_lt_four {l : ℕ} (a : Fin l → Bool) (hl : l ≤ 2) :
    (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0 < 4 := by
  rw [RowFromCoins.assignmentFold_eq_two a hl]
  have h₀ := Bool.toNat_le ((List.ofFn a).getD 0 false)
  have h₁ := Bool.toNat_le ((List.ofFn a).getD 1 false)
  omega

/-- For `l ≤ 2`, the assignment fold is below the exact code count `2^l`.
Thus unused codes begin at one for arity zero and at two for arity one. -/
theorem assignmentFold_lt_pow {l : ℕ} (a : Fin l → Bool) (hl : l ≤ 2) :
    (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0 < 2 ^ l := by
  have hc : l = 0 ∨ l = 1 ∨ l = 2 := by omega
  rcases hc with rfl | rfl | rfl
  · rw [RowFromCoins.assignmentFold_eq_two a (by decide),
      List.getD_eq_default (List.ofFn a) false (n := 0) (by rw [List.length_ofFn]),
      List.getD_eq_default (List.ofFn a) false (n := 1) (by rw [List.length_ofFn]; omega)]
    decide
  · rw [RowFromCoins.assignmentFold_eq_two a (by decide),
      List.getD_eq_default (List.ofFn a) false (n := 1) (by rw [List.length_ofFn])]
    simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero]
    exact Bool.toNat_lt _
  · exact assignmentFold_lt_four a (by decide)

/-- For at most two positions, equal assignment folds imply equal assignments.

**Proof sketch.** The published two-bit formula writes each fold as `b₀ + 2 b₁`.
The bounds `b₀,b₁ ≤ 1` uniquely recover both natural-valued bits. Testing each
bit value for equality with one recovers the Boolean bits. Every valid position
is zero or one, so the public `ofFn` element readers recover the whole assignment. -/
theorem assignmentFold_injective (l : ℕ) (hl : l ≤ 2) :
    Function.Injective (fun a : Fin l → Bool =>
      (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) := by
  intro a b hab
  change (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0 =
    (List.ofFn b).foldr (fun b k => b.toNat + 2 * k) 0 at hab
  rw [RowFromCoins.assignmentFold_eq_two a hl, RowFromCoins.assignmentFold_eq_two b hl] at hab
  -- Recover both binary digits from the weighted sum.
  have ha₀ := Bool.toNat_le ((List.ofFn a).getD 0 false)
  have ha₁ := Bool.toNat_le ((List.ofFn a).getD 1 false)
  have hb₀ := Bool.toNat_le ((List.ofFn b).getD 0 false)
  have hb₁ := Bool.toNat_le ((List.ofFn b).getD 1 false)
  have h₀ : ((List.ofFn a).getD 0 false).toNat = ((List.ofFn b).getD 0 false).toNat := by
    omega
  have h₁ : ((List.ofFn a).getD 1 false).toNat = ((List.ofFn b).getD 1 false).toNat := by
    omega
  have h₀' : (List.ofFn a).getD 0 false = (List.ofFn b).getD 0 false := by
    simpa only [Bool.toNat_eq_one, Bool.decide_eq_true] using
      congrArg (fun q : ℕ => decide (q = 1)) h₀
  have h₁' : (List.ofFn a).getD 1 false = (List.ofFn b).getD 1 false := by
    simpa only [Bool.toNat_eq_one, Bool.decide_eq_true] using
      congrArg (fun q : ℕ => decide (q = 1)) h₁
  -- Every assignment position is one of the recovered two digits.
  funext t
  have ht : (t : ℕ) = 0 ∨ (t : ℕ) = 1 := by have := t.isLt; omega
  have hget : (List.ofFn a).getD t false = (List.ofFn b).getD t false := by
    rcases ht with ht | ht
    · simpa only [ht] using h₀'
    · simpa only [ht] using h₁'
  rw [List.getD_eq_getElem (List.ofFn a) false (n := (t : ℕ)) (by rw [List.length_ofFn]; exact t.isLt),
    List.getD_eq_getElem (List.ofFn b) false (n := (t : ℕ)) (by rw [List.length_ofFn]; exact t.isLt),
    List.getElem_ofFn, List.getElem_ofFn] at hget
  exact hget

/-- Embed an assignment to `l ≤ 2` positions in four row codes by its binary fold. -/
def assignmentEmbedding (l : ℕ) (hl : l ≤ 2) : (Fin l → Bool) ↪ Fin 4 where
  toFun a := ⟨(List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0,
    assignmentFold_lt_four a hl⟩
  inj' _ _ h := assignmentFold_injective l hl (congrArg Fin.val h)

/-- The natural value of `assignmentEmbedding l hl a` is its assignment fold. -/
theorem assignmentEmbedding_eq (l : ℕ) (hl : l ≤ 2) (a : Fin l → Bool) :
    (assignmentEmbedding l hl a : ℕ) =
      (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0 := rfl

/-- The embedded code is below `2^l`: `(assignmentEmbedding l hl a : ℕ) < 2^l`. -/
theorem assignmentEmbedding_lt_pow (l : ℕ) (hl : l ≤ 2) (a : Fin l → Bool) :
    (assignmentEmbedding l hl a : ℕ) < 2 ^ l := assignmentFold_lt_pow a hl

/-- Extend assignment XOR to four row codes with the existing embedding extension.
Every code outside the assignment embedding's range is fixed. -/
def assignmentPerm (l : ℕ) (hl : l ≤ 2) (mask : Fin l → Bool) : Equiv.Perm (Fin 4) :=
  (xorPerm mask).viaFintypeEmbedding (assignmentEmbedding l hl)

/-- `assignmentPerm l hl mask` is `xorPerm mask` extended through the fold embedding. -/
theorem assignmentPerm_eq (l : ℕ) (hl : l ≤ 2) (mask : Fin l → Bool) :
    assignmentPerm l hl mask =
      (xorPerm mask).viaFintypeEmbedding (assignmentEmbedding l hl) := rfl

/-- The extended permutation sends the code of `a` to the code of `a XOR mask`. -/
theorem assignmentPerm_code (l : ℕ) (hl : l ≤ 2) (mask a : Fin l → Bool) :
    assignmentPerm l hl mask (assignmentEmbedding l hl a) =
      assignmentEmbedding l hl (xorPerm mask a) := by
  rw [assignmentPerm_eq, Equiv.Perm.viaFintypeEmbedding_apply_image]

/-- The extension fixes every code `a ≥ 2^l`. In particular, arity zero fixes
codes one through three, and arity one fixes codes two and three. -/
theorem assignmentPerm_unused (l : ℕ) (hl : l ≤ 2) (mask : Fin l → Bool)
    (a : Fin 4) (ha : 2 ^ l ≤ (a : ℕ)) : assignmentPerm l hl mask a = a := by
  rw [assignmentPerm_eq]
  apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
  rintro ⟨b, hb⟩
  have hval := congrArg Fin.val hb
  have hlt := assignmentEmbedding_lt_pow l hl b
  omega

/-- The padded key-choice mask is `v w` at real vertices and `false` elsewhere. -/
def keyMask {m : ℕ} (C : DAGCircuit m) (S : ℕ) (v : ℕ → Bool) (w : Fin S) : Bool :=
  if (w : ℕ) < C.size then v w else false

/-- `keyMask C S v w = if w < C.size then v w else false`. -/
theorem keyMask_eq {m : ℕ} (C : DAGCircuit m) (S : ℕ) (v : ℕ → Bool) (w : Fin S) :
    keyMask C S v w = if (w : ℕ) < C.size then v w else false := rfl

/-- A real vertex's padded key mask is its wire value: `keyMask ... w = v w`. -/
theorem keyMask_vertex {m : ℕ} (C : DAGCircuit m) (S : ℕ) (v : ℕ → Bool)
    (hS : C.size ≤ S) (w : Fin C.size) :
    keyMask C S v (Fin.castLE hS w) = v w := by
  change (if (w : ℕ) < C.size then v w else false) = v w
  rw [if_pos w.isLt]

/-- The padded row permutation extends assignment XOR at each real gate and
is the identity at unused gate coordinates. -/
def rowPerm {m : ℕ} (C : DAGCircuit m) (S : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2)
    (v : ℕ → Bool) (i : Fin S) : Equiv.Perm (Fin 4) :=
  if hi : (i : ℕ) < C.gates.length then
    assignmentPerm (C.gates[(i : ℕ)]'hi).args.length (hA ⟨i, hi⟩)
      (RelabelGarbling.argValues C v ⟨i, hi⟩)
  else Equiv.refl _

/-- `rowPerm C S hA v i` is the real gate's extended assignment XOR, or the identity. -/
theorem rowPerm_eq {m : ℕ} (C : DAGCircuit m) (S : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2)
    (v : ℕ → Bool) (i : Fin S) :
    rowPerm C S hA v i =
      if hi : (i : ℕ) < C.gates.length then
        assignmentPerm (C.gates[(i : ℕ)]'hi).args.length (hA ⟨i, hi⟩)
          (RelabelGarbling.argValues C v ⟨i, hi⟩)
      else Equiv.refl _ := rfl

/-- At a real gate, the padded row permutation is precisely that gate's
assignment-XOR extension. -/
theorem rowPerm_gate {m : ℕ} (C : DAGCircuit m) (S : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2) (v : ℕ → Bool)
    (hG : C.gates.length ≤ S) (i : Fin C.gates.length) :
    rowPerm C S hA v (Fin.castLE hG i) =
      assignmentPerm (C.gates[i]).args.length (hA i) (RelabelGarbling.argValues C v i) := by
  rw [rowPerm_eq, dif_pos i.isLt]

/-- On an embedded assignment code, the padded row permutation returns the
binary fold of the XORed assignment at that gate. -/
theorem rowPerm_fold {m : ℕ} (C : DAGCircuit m) (S : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2) (v : ℕ → Bool)
    (hG : C.gates.length ≤ S) (i : Fin C.gates.length)
    (a : Fin (C.gates[i]).args.length → Bool) :
    (rowPerm C S hA v (Fin.castLE hG i)
        (assignmentEmbedding (C.gates[i]).args.length (hA i) a) : ℕ) =
      (List.ofFn (xorPerm (RelabelGarbling.argValues C v i) a)).foldr
        (fun b k => b.toNat + 2 * k) 0 := by
  rw [rowPerm_gate, assignmentPerm_code, assignmentEmbedding_eq]

/-- The padded shift mask is the value of the argument at a real gate/position,
and is `false` at unused gate or argument positions. -/
def shiftMask {m : ℕ} (C : DAGCircuit m) (S : ℕ) (v : ℕ → Bool)
    (i : Fin S) (t : Fin 2) : Bool :=
  if hi : (i : ℕ) < C.gates.length then
    if ht : (t : ℕ) < (C.gates[(i : ℕ)]'hi).args.length then
      v ((C.gates[(i : ℕ)]'hi).args[(t : ℕ)]'ht)
    else false
  else false

/-- `shiftMask` reads the real argument's wire value and returns `false` elsewhere. -/
theorem shiftMask_eq {m : ℕ} (C : DAGCircuit m) (S : ℕ) (v : ℕ → Bool)
    (i : Fin S) (t : Fin 2) :
    shiftMask C S v i t =
      if hi : (i : ℕ) < C.gates.length then
        if ht : (t : ℕ) < (C.gates[(i : ℕ)]'hi).args.length then
          v ((C.gates[(i : ℕ)]'hi).args[(t : ℕ)]'ht)
        else false
      else false := rfl

/-- At a real gate and argument position, the padded shift mask is the value
of that argument's wire. -/
theorem shiftMask_argument {m : ℕ} (C : DAGCircuit m) (S : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2) (v : ℕ → Bool)
    (hG : C.gates.length ≤ S) (i : Fin C.gates.length)
    (t : Fin (C.gates[i]).args.length) :
    shiftMask C S v (Fin.castLE hG i) (Fin.castLE (hA i) t) =
      v ((C.gates[i]).args[t]) := by
  rw [shiftMask_eq, dif_pos i.isLt, dif_pos t.isLt]

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel
