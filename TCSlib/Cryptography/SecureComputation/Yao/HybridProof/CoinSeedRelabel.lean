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
This is the first conjunct of the published `GarblingProbability.assignmentFold_small`.
[PS10, Protocol 162.6]
`(List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0 < 4`. -/
theorem assignmentFold_lt_four {l : ℕ} (a : Fin l → Bool) (hl : l ≤ 2) :
    (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0 < 4 :=
  (GarblingProbability.assignmentFold_small l hl).1 a

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

/-- For at most two positions, equal assignment folds imply equal assignments. This is the
second conjunct of the published `GarblingProbability.assignmentFold_small`.
`Function.Injective (fun a : Fin l → Bool => (List.ofFn a).foldr (fun b k => b.toNat + 2 * k)
0)`. -/
theorem assignmentFold_injective (l : ℕ) (hl : l ≤ 2) :
    Function.Injective (fun a : Fin l → Bool =>
      (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) :=
  (GarblingProbability.assignmentFold_small l hl).2

/-- Embed an assignment to `l ≤ 2` positions in four row codes by its binary fold. -/
def assignmentEmbedding (l : ℕ) (hl : l ≤ 2) : (Fin l → Bool) ↪ Fin 4 where
  toFun a := ⟨(List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0,
    assignmentFold_lt_four a hl⟩
  inj' _ _ h := assignmentFold_injective l hl (congrArg Fin.val h)

/-- The natural value of `assignmentEmbedding l hl a` is its assignment fold.
`(assignmentEmbedding l hl a : ℕ) = (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0`. -/
theorem assignmentEmbedding_eq (l : ℕ) (hl : l ≤ 2) (a : Fin l → Bool) :
    (assignmentEmbedding l hl a : ℕ) =
      (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0 := rfl

/-- The embedded code is below `2^l`: `(assignmentEmbedding l hl a : ℕ) < 2^l`. -/
theorem assignmentEmbedding_lt_pow (l : ℕ) (hl : l ≤ 2) (a : Fin l → Bool) :
    (assignmentEmbedding l hl a : ℕ) < 2 ^ l := assignmentFold_lt_pow a hl

/-- Extend assignment XOR to four row codes with the existing embedding extension.
Every code outside the assignment embedding's range is fixed.
`assignmentPerm l hl mask = (xorPerm mask).viaFintypeEmbedding (assignmentEmbedding l hl)`. -/
def assignmentPerm (l : ℕ) (hl : l ≤ 2) (mask : Fin l → Bool) : Equiv.Perm (Fin 4) :=
  (xorPerm mask).viaFintypeEmbedding (assignmentEmbedding l hl)

/-- `assignmentPerm l hl mask` is `xorPerm mask` extended through the fold embedding.
`assignmentPerm l hl mask = (xorPerm mask).viaFintypeEmbedding (assignmentEmbedding l hl)`. -/
theorem assignmentPerm_eq (l : ℕ) (hl : l ≤ 2) (mask : Fin l → Bool) :
    assignmentPerm l hl mask =
      (xorPerm mask).viaFintypeEmbedding (assignmentEmbedding l hl) := rfl

/-- The extended permutation sends the code of `a` to the code of `a XOR mask`.
`assignmentPerm l hl mask (assignmentEmbedding l hl a) = assignmentEmbedding l hl (xorPerm mask
a)`. -/
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

/-- The padded key-choice mask is `v w` at real vertices and `false` elsewhere.
`keyMask C S v w = if (w : ℕ) < C.size then v w else false`. -/
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
is the identity at unused gate coordinates.
`rowPerm C S hA v i = if hi : (i : ℕ) < C.gates.length then assignmentPerm (C.gates[(i :
ℕ)]'hi).args.length (hA ⟨i, hi⟩) (RelabelGarbling.argValues C v ⟨i, hi⟩) else Equiv.refl _`. -/
def rowPerm {m : ℕ} (C : DAGCircuit m) (S : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2)
    (v : ℕ → Bool) (i : Fin S) : Equiv.Perm (Fin 4) :=
  if hi : (i : ℕ) < C.gates.length then
    assignmentPerm (C.gates[(i : ℕ)]'hi).args.length (hA ⟨i, hi⟩)
      (RelabelGarbling.argValues C v ⟨i, hi⟩)
  else Equiv.refl _

/-- `rowPerm C S hA v i` is the real gate's extended assignment XOR, or the identity.
`rowPerm C S hA v i = if hi : (i : ℕ) < C.gates.length then assignmentPerm (C.gates[(i :
ℕ)]'hi).args.length (hA ⟨i, hi⟩) (RelabelGarbling.argValues C v ⟨i, hi⟩) else Equiv.refl _`. -/
theorem rowPerm_eq {m : ℕ} (C : DAGCircuit m) (S : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2)
    (v : ℕ → Bool) (i : Fin S) :
    rowPerm C S hA v i =
      if hi : (i : ℕ) < C.gates.length then
        assignmentPerm (C.gates[(i : ℕ)]'hi).args.length (hA ⟨i, hi⟩)
          (RelabelGarbling.argValues C v ⟨i, hi⟩)
      else Equiv.refl _ := rfl

/-- At a real gate, the padded row permutation is precisely that gate's
assignment-XOR extension.
`rowPerm C S hA v (Fin.castLE hG i) = assignmentPerm (C.gates[i]).args.length (hA i)
(RelabelGarbling.argValues C v i)`. -/
theorem rowPerm_gate {m : ℕ} (C : DAGCircuit m) (S : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2) (v : ℕ → Bool)
    (hG : C.gates.length ≤ S) (i : Fin C.gates.length) :
    rowPerm C S hA v (Fin.castLE hG i) =
      assignmentPerm (C.gates[i]).args.length (hA i) (RelabelGarbling.argValues C v i) := by
  change (if hi : (i : ℕ) < C.gates.length then
    assignmentPerm (C.gates[(i : ℕ)]'hi).args.length (hA ⟨i, hi⟩)
      (RelabelGarbling.argValues C v ⟨i, hi⟩)
    else Equiv.refl _) = _
  rw [dif_pos i.isLt]
  simp only [Fin.getElem_fin]

/-- On an embedded assignment code, the padded row permutation returns the
binary fold of the XORed assignment at that gate.
`(rowPerm C S hA v (Fin.castLE hG i) (assignmentEmbedding (C.gates[i]).args.length (hA i) a) : ℕ) =
(List.ofFn (xorPerm (RelabelGarbling.argValues C v i) a)).foldr (fun b k => b.toNat + 2 * k) 0`. -/
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
and is `false` at unused gate or argument positions.
`shiftMask C S v i t = if hi : (i : ℕ) < C.gates.length then if ht : (t : ℕ) < (C.gates[(i :
ℕ)]'hi).args.length then v ((C.gates[(i : ℕ)]'hi).args[(t : ℕ)]'ht) else false else false`. -/
def shiftMask {m : ℕ} (C : DAGCircuit m) (S : ℕ) (v : ℕ → Bool)
    (i : Fin S) (t : Fin 2) : Bool :=
  if hi : (i : ℕ) < C.gates.length then
    if ht : (t : ℕ) < (C.gates[(i : ℕ)]'hi).args.length then
      v ((C.gates[(i : ℕ)]'hi).args[(t : ℕ)]'ht)
    else false
  else false

/-- `shiftMask` reads the real argument's wire value and returns `false` elsewhere.
`shiftMask C S v i t = if hi : (i : ℕ) < C.gates.length then if ht : (t : ℕ) < (C.gates[(i :
ℕ)]'hi).args.length then v ((C.gates[(i : ℕ)]'hi).args[(t : ℕ)]'ht) else false else false`. -/
theorem shiftMask_eq {m : ℕ} (C : DAGCircuit m) (S : ℕ) (v : ℕ → Bool)
    (i : Fin S) (t : Fin 2) :
    shiftMask C S v i t =
      if hi : (i : ℕ) < C.gates.length then
        if ht : (t : ℕ) < (C.gates[(i : ℕ)]'hi).args.length then
          v ((C.gates[(i : ℕ)]'hi).args[(t : ℕ)]'ht)
        else false
      else false := rfl

/-- At a real gate and argument position, the padded shift mask is the value
of that argument's wire.
`shiftMask C S v (Fin.castLE hG i) (Fin.castLE (hA i) t) = v ((C.gates[i]).args[t])`. -/
theorem shiftMask_argument {m : ℕ} (C : DAGCircuit m) (S : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2) (v : ℕ → Bool)
    (hG : C.gates.length ≤ S) (i : Fin C.gates.length)
    (t : Fin (C.gates[i]).args.length) :
    shiftMask C S v (Fin.castLE hG i) (Fin.castLE (hA i) t) =
      v ((C.gates[i]).args[t]) := by
  change (if hi : (i : ℕ) < C.gates.length then
    if ht : (t : ℕ) < (C.gates[(i : ℕ)]'hi).args.length then
      v ((C.gates[(i : ℕ)]'hi).args[(t : ℕ)]'ht)
    else false
    else false) = _
  rw [dif_pos i.isLt]
  simp only [Fin.getElem_fin] at t ⊢
  rw [dif_pos t.isLt]

/-- Every unused key coordinate has mask `false`, so its entire block is fixed.
`keyMask C S v w = false`. -/
theorem keyMask_unused {m : ℕ} (C : DAGCircuit m) (S : ℕ) (v : ℕ → Bool)
    (w : Fin S) (hw : C.size ≤ (w : ℕ)) : keyMask C S v w = false := by
  rw [keyMask_eq, if_neg (Nat.not_lt.mpr hw)]

/-- At an unused gate coordinate, the padded row action is the identity.
`rowPerm C S hA v i = Equiv.refl _`. -/
theorem rowPerm_unused_gate {m : ℕ} (C : DAGCircuit m) (S : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2) (v : ℕ → Bool)
    (i : Fin S) (hi : C.gates.length ≤ (i : ℕ)) :
    rowPerm C S hA v i = Equiv.refl _ := by
  rw [rowPerm_eq, dif_neg (Nat.not_lt.mpr hi)]

/-- At a real gate, every unused row code `a ≥ 2^arity` is fixed. -/
theorem rowPerm_unused_code {m : ℕ} (C : DAGCircuit m) (S : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2) (v : ℕ → Bool)
    (hG : C.gates.length ≤ S) (i : Fin C.gates.length) (a : Fin 4)
    (ha : 2 ^ (C.gates[i]).args.length ≤ (a : ℕ)) :
    rowPerm C S hA v (Fin.castLE hG i) a = a := by
  rw [rowPerm_gate]
  exact assignmentPerm_unused _ (hA i) _ a ha

/-- At an unused gate coordinate, every shift mask bit is `false`.
`shiftMask C S v i t = false`. -/
theorem shiftMask_unused_gate {m : ℕ} (C : DAGCircuit m) (S : ℕ) (v : ℕ → Bool)
    (i : Fin S) (t : Fin 2) (hi : C.gates.length ≤ (i : ℕ)) :
    shiftMask C S v i t = false := by
  rw [shiftMask_eq, dif_neg (Nat.not_lt.mpr hi)]

/-- At a real gate but unused argument coordinate, the shift mask bit is `false`.
`shiftMask C S v (Fin.castLE hG i) t = false`. -/
theorem shiftMask_unused_argument {m : ℕ} (C : DAGCircuit m) (S : ℕ) (v : ℕ → Bool)
    (hG : C.gates.length ≤ S) (i : Fin C.gates.length) (t : Fin 2)
    (ht : (C.gates[i]).args.length ≤ (t : ℕ)) :
    shiftMask C S v (Fin.castLE hG i) t = false := by
  change (if hi : (i : ℕ) < C.gates.length then
    if ht' : (t : ℕ) < (C.gates[(i : ℕ)]'hi).args.length then
      v ((C.gates[(i : ℕ)]'hi).args[(t : ℕ)]'ht')
    else false
    else false) = false
  rw [dif_pos i.isLt]
  simp only [Fin.getElem_fin] at ht
  rw [dif_neg (Nat.not_lt.mpr ht)]

/-- At each real vertex, relabeling changes the key tape address from choice `b`
to choice `b XOR v w`, retaining its vertex and within-key coordinate.
`(List.ofFn (CoinRelabel.relabel S n (keyMask C S v) (rowPerm C S hA v) (shiftMask C S v) r)).getD
((b.toNat * S + w) * n + t) false = (List.ofFn r).getD (((xor b (v w)).toNat * S + w) * n + t)
false`. -/
theorem relabel_key_getD {m : ℕ} (C : DAGCircuit m) (S n : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2) (v : ℕ → Bool)
    (hS : C.size ≤ S) (r : Fin (10 * S * n + 2 * S) → Bool)
    (w : Fin C.size) (b : Bool) (t : Fin n) :
    (List.ofFn (CoinRelabel.relabel S n (keyMask C S v)
      (rowPerm C S hA v) (shiftMask C S v) r)).getD
        ((b.toNat * S + w) * n + t) false =
      (List.ofFn r).getD (((xor b (v w)).toNat * S + w) * n + t) false := by
  have h := CoinRelabel.relabel_key_getD S n (keyMask C S v)
    (rowPerm C S hA v) (shiftMask C S v) r b (Fin.castLE hS w) t
  rw [keyMask_vertex C S v hS w] at h
  exact h

/-- At a real gate, relabeling sends a row's nonce address to the binary fold
of its argument-value-XORed assignment, leaving the within-row bit unchanged.
`(List.ofFn (CoinRelabel.relabel S n (keyMask C S v) (rowPerm C S hA v) (shiftMask C S v) r)).getD
(2 * S * n + (4 * i + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + t) false =
(List.ofFn r).getD (2 * S * n + (4 * i + (List.ofFn (xorPerm (RelabelGarbling.argValues C v i)
a)).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + t) false`. -/
theorem relabel_row_getD {m : ℕ} (C : DAGCircuit m) (S n : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2) (v : ℕ → Bool)
    (hG : C.gates.length ≤ S) (r : Fin (10 * S * n + 2 * S) → Bool)
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool)
    (t : Fin (2 * n)) :
    (List.ofFn (CoinRelabel.relabel S n (keyMask C S v)
      (rowPerm C S hA v) (shiftMask C S v) r)).getD
        (2 * S * n + (4 * i +
          (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + t) false =
      (List.ofFn r).getD (2 * S * n + (4 * i +
        (List.ofFn (xorPerm (RelabelGarbling.argValues C v i) a)).foldr
          (fun b k => b.toNat + 2 * k) 0) * (2 * n) + t) false := by
  have h := CoinRelabel.relabel_row_getD S n (keyMask C S v)
    (rowPerm C S hA v) (shiftMask C S v) r (Fin.castLE hG i)
      (assignmentEmbedding (C.gates[i]).args.length (hA i) a) t
  rw [rowPerm_fold, assignmentEmbedding_eq] at h
  exact h

/-- At a real gate and argument, the relabeled shift tape bit is the original
bit XOR the value of the wire at that argument. The result includes `n = 0`. -/
theorem relabel_shift_getD {m : ℕ} (C : DAGCircuit m) (S n : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2) (v : ℕ → Bool)
    (hG : C.gates.length ≤ S) (r : Fin (10 * S * n + 2 * S) → Bool)
    (i : Fin C.gates.length) (t : Fin (C.gates[i]).args.length) :
    (List.ofFn (CoinRelabel.relabel S n (keyMask C S v)
      (rowPerm C S hA v) (shiftMask C S v) r)).getD
        (10 * S * n + 2 * i + t) false =
      xor ((List.ofFn r).getD (10 * S * n + 2 * i + t) false)
        (v ((C.gates[i]).args[t])) := by
  have h := CoinRelabel.relabel_shift_getD S n (keyMask C S v)
    (rowPerm C S hA v) (shiftMask C S v) r (Fin.castLE hG i) (Fin.castLE (hA i) t)
  rw [shiftMask_argument] at h
  exact h

/-- A seed specified by the key, two nonce halves and permutation-bit readers
commutes exactly with complete-tape relabeling. No positive key width is assumed.
This identifies the actual sampler with the generic seed relabeling, rather than
introducing a second sampler. [PS10, Theorem 163.7]
`seed (List.ofFn (CoinRelabel.relabel S n (keyMask C S v) (rowPerm C S hA v) (shiftMask C S v) r)) =
RelabelGarbling.relabelSeed C v (seed (List.ofFn r))`.

**Proof sketch.** Equality of seeds reduces to equality of keys, row-coin pairs
and row permutations. Each key coordinate follows the key-address transformation.
Each nonce half follows the row-address transformation, using the embedded binary
assignment code. The shift-bit transformation composes the old assignment XOR
with argument-value XOR, which is exactly the relabeled permutation. -/
theorem seed_relabel {m : ℕ} (C : DAGCircuit m) (S n : ℕ)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2) (v : ℕ → Bool)
    (hS : C.size ≤ S)
    (seed : List Bool → GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
    (hK : ∀ q (w : Fin C.size) b (t : Fin n),
      (seed q).1 w b t = q.getD ((b.toNat * S + w) * n + t) false)
    (hR₀ : ∀ q (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool)
        (t : Fin n),
      ((seed q).2.1 i a).1 t = q.getD (2 * S * n + (4 * i +
        (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + t) false)
    (hR₁ : ∀ q (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool)
        (t : Fin n),
      ((seed q).2.1 i a).2 t = q.getD (2 * S * n + (4 * i +
        (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + n + t) false)
    (hP : ∀ q (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool)
        (t : Fin (C.gates[i]).args.length),
      (seed q).2.2 i a t = xor (a t) (q.getD (10 * S * n + 2 * i + t) false))
    (r : Fin (10 * S * n + 2 * S) → Bool) :
    seed (List.ofFn (CoinRelabel.relabel S n (keyMask C S v)
        (rowPerm C S hA v) (shiftMask C S v) r)) =
      RelabelGarbling.relabelSeed C v (seed (List.ofFn r)) := by
  have hG : C.gates.length ≤ S := by
    rw [DAGCircuit.size_eq] at hS
    omega
  apply Prod.ext
  · funext w b t
    rw [RelabelGarbling.relabelSeed_key, hK, hK]
    exact relabel_key_getD C S n hA v hS r w b t
  · apply Prod.ext
    · funext i a
      rw [RelabelGarbling.relabelSeed_coin]
      apply Prod.ext
      · funext t
        rw [hR₀, hR₀]
        exact relabel_row_getD C S n hA v hG r i a
          ⟨t, by have := t.isLt; omega⟩
      · funext t
        rw [hR₁, hR₁]
        simpa only [Nat.add_assoc] using
          relabel_row_getD C S n hA v hG r i a
            ⟨n + t, by have := t.isLt; omega⟩
    · funext i
      apply Equiv.ext
      intro a
      funext t
      rw [RelabelGarbling.relabelSeed_perm]
      simp only [xorPerm_apply, hP, relabel_shift_getD C S n hA v hG r i t,
        RelabelGarbling.argValues_apply, Bool.xor_assoc]

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel
