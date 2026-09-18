/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Log
import TCSlib.Complexity.CircuitComplexity.NCAC

/-!
# `PARITY` is in `NC¹`

## Main definitions

* `BoolCircuit.parityCircuit` — the balanced binary XOR tree on `n` input bits.
* `Language.parity` — [AB09, Ex 6.26]'s `PARITY = {x : x has an odd number of 1s}`.

## Main results

* `Language.parity_inNC_one` — [AB09, Ex 6.26], `PARITY ∈ NC¹`.
* `BoolCircuit.parityCircuit_eval`, `_maxFanin_le`, `_depth_le`, `_size_le` — the four
  facts that membership needs; `_eval_zero` and `_eval_one` pin the two input lengths at
  which `Nat.log 2 n = 0`.
* `Language.mem_parity_iff` — `PARITY` membership as the iterated XOR of the letters.

## Divergences from Arora–Barak Example 6.26

* **Dual pairs.** AB's tree has an XOR gate at every internal node.  `Circuit`'s gates are
  `AND` and `OR` and it negates only at literals, so each node here carries a *pair* — a
  circuit for the XOR of its leaves and a circuit for the complement — and `xorNode` builds
  a parent pair from its children's as `(a ∧ b') ∨ (a' ∧ b)` and `(a ∧ b) ∨ (a' ∧ b')`.
  That costs two levels per halving where AB's costs one, so the depth is `2⌈log₂ n⌉ + 2`
  against AB's `⌈log₂ n⌉`.  Both are `O(log n)`, which is all `NC¹` asks.
* **Constants.** `4 * (Nat.log 2 n + 1)` for depth and `32 * (n + 1) ^ 4` for size are what
  this construction gives.  AB states neither and neither is claimed optimal.  The size
  bound is not a separate recurrence: it is read off the depth bound and fan-in `2` through
  `Circuit.size_succ_le_two_pow`.
* **Fan-out 1, and the size measure.** Both are inherited from, and recorded in,
  `TCSlib.Complexity.CircuitComplexity.NCAC`.  `NC¹` here is that file's `Language.InNC 1`,
  which is AB's `NC¹` restricted to fan-out 1; no comparison with AB's DAG class is
  formalized there or here.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

variable {n : ℕ}

/-- The XOR of two circuits, as a pair of a circuit and a circuit for its complement. -/
private def xorNode (p q : Circuit n × Circuit n) : Circuit n × Circuit n :=
  (Circuit.node false [Circuit.node true [p.1, q.2], Circuit.node true [p.2, q.1]],
   Circuit.node false [Circuit.node true [p.1, q.1], Circuit.node true [p.2, q.2]])

/-- A pair is dual when its second component computes the negation of its first. -/
private def IsDual (x : Fin n → Bool) (p : Circuit n × Circuit n) : Prop :=
  p.2.eval x = !p.1.eval x

/-- `xorNode` computes the XOR of the two first components. -/
private theorem xorNode_eval {x : Fin n → Bool} {p q : Circuit n × Circuit n}
    (hp : IsDual x p) (hq : IsDual x q) :
    (xorNode p q).1.eval x = Bool.xor (p.1.eval x) (q.1.eval x) := by
  simp only [xorNode, Circuit.eval, List.foldr_cons, List.foldr_nil]
  rw [show q.2.eval x = !q.1.eval x from hq, show p.2.eval x = !p.1.eval x from hp]
  cases p.1.eval x <;> cases q.1.eval x <;> simp

/-- `xorNode` again produces a dual pair. -/
private theorem xorNode_isDual {x : Fin n → Bool} {p q : Circuit n × Circuit n}
    (hp : IsDual x p) (hq : IsDual x q) : IsDual x (xorNode p q) := by
  simp only [IsDual, xorNode, Circuit.eval, List.foldr_cons, List.foldr_nil]
  rw [show q.2.eval x = !q.1.eval x from hq, show p.2.eval x = !p.1.eval x from hp]
  cases p.1.eval x <;> cases q.1.eval x <;> simp

/-- The XOR of the first components of a list of pairs. -/
private def xorAll (x : Fin n → Bool) (ps : List (Circuit n × Circuit n)) : Bool :=
  ps.foldr (fun p acc => Bool.xor (p.1.eval x) acc) false

/-- Maximum depth over both components of a list of pairs. -/
private def pairDepth (ps : List (Circuit n × Circuit n)) : ℕ :=
  ps.foldr (fun p acc => max (max p.1.depth p.2.depth) acc) 0

/-- Maximum fan-in over both components of a list of pairs. -/
private def pairFanin (ps : List (Circuit n × Circuit n)) : ℕ :=
  ps.foldr (fun p acc => max (max p.1.maxFanin p.2.maxFanin) acc) 0

/-- `xorAll` on a cons cell. -/
private theorem xorAll_cons (x : Fin n → Bool) (p : Circuit n × Circuit n)
    (ps : List (Circuit n × Circuit n)) :
    xorAll x (p :: ps) = Bool.xor (p.1.eval x) (xorAll x ps) := rfl

/-- `pairDepth` on a cons cell. -/
private theorem pairDepth_cons (p : Circuit n × Circuit n)
    (ps : List (Circuit n × Circuit n)) :
    pairDepth (p :: ps) = max (max p.1.depth p.2.depth) (pairDepth ps) := rfl

/-- `pairFanin` on a cons cell. -/
private theorem pairFanin_cons (p : Circuit n × Circuit n)
    (ps : List (Circuit n × Circuit n)) :
    pairFanin (p :: ps) = max (max p.1.maxFanin p.2.maxFanin) (pairFanin ps) := rfl

/-- `xorNode` costs two levels of depth. -/
private theorem pairDepth_xorNode (p q : Circuit n × Circuit n) :
    max (xorNode p q).1.depth (xorNode p q).2.depth
      ≤ 2 + max (max p.1.depth p.2.depth) (max q.1.depth q.2.depth) := by
  simp only [xorNode, Circuit.depth_node, Circuit.maxDepth_cons, Circuit.maxDepth_nil]
  omega

/-- `xorNode` introduces only fan-in-2 gates. -/
private theorem pairFanin_xorNode (p q : Circuit n × Circuit n) :
    max (xorNode p q).1.maxFanin (xorNode p q).2.maxFanin
      ≤ max 2 (max (max p.1.maxFanin p.2.maxFanin) (max q.1.maxFanin q.2.maxFanin)) := by
  simp only [xorNode, Circuit.maxFanin_node, Circuit.maxFaninL_cons, Circuit.maxFaninL_nil,
    List.length_cons, List.length_nil]
  omega

/-- Pair adjacent entries and XOR each pair. -/
private def xorPairUp : List (Circuit n × Circuit n) → List (Circuit n × Circuit n)
  | [] => []
  | [p] => [p]
  | p :: q :: ps => xorNode p q :: xorPairUp ps

/-- Pairing halves the list, rounding up. -/
private theorem length_xorPairUp :
    ∀ ps : List (Circuit n × Circuit n), (xorPairUp ps).length = (ps.length + 1) / 2
  | [] => by simp [xorPairUp]
  | [_] => by simp [xorPairUp]
  | _ :: _ :: ps => by
      have := length_xorPairUp ps
      simp only [xorPairUp, List.length_cons] at *
      omega

/-- Pairing preserves duality. -/
private theorem isDual_xorPairUp (x : Fin n → Bool) :
    ∀ ps : List (Circuit n × Circuit n), (∀ p ∈ ps, IsDual x p) →
      ∀ p ∈ xorPairUp ps, IsDual x p
  | [], _ => by simp [xorPairUp]
  | [p], h => by simpa [xorPairUp] using h p (by simp)
  | p :: q :: ps, h => by
      have ih := isDual_xorPairUp x ps (fun r hr => h r (by simp [hr]))
      intro r hr
      rcases List.mem_cons.mp (by simpa [xorPairUp] using hr) with rfl | hr'
      · exact xorNode_isDual (h p (by simp)) (h q (by simp))
      · exact ih r hr'

/-- Pairing preserves the overall XOR. -/
private theorem xorAll_xorPairUp (x : Fin n → Bool) :
    ∀ ps : List (Circuit n × Circuit n), (∀ p ∈ ps, IsDual x p) →
      xorAll x (xorPairUp ps) = xorAll x ps
  | [], _ => rfl
  | [_], _ => rfl
  | p :: q :: ps, h => by
      have ih := xorAll_xorPairUp x ps (fun r hr => h r (by simp [hr]))
      simp only [xorPairUp, xorAll_cons]
      rw [xorNode_eval (h p (by simp)) (h q (by simp)), ih, Bool.xor_assoc]

/-- Pairing adds two to the depth. -/
private theorem pairDepth_xorPairUp :
    ∀ ps : List (Circuit n × Circuit n), pairDepth (xorPairUp ps) ≤ 2 + pairDepth ps
  | [] => by simp [xorPairUp, pairDepth]
  | [p] => by simp [xorPairUp, pairDepth_cons]
  | p :: q :: ps => by
      have ih := pairDepth_xorPairUp ps
      have hn := pairDepth_xorNode p q
      simp only [xorPairUp, pairDepth_cons]
      omega

/-- Pairing introduces only fan-in-2 gates. -/
private theorem pairFanin_xorPairUp :
    ∀ ps : List (Circuit n × Circuit n), pairFanin (xorPairUp ps) ≤ max 2 (pairFanin ps)
  | [] => by simp [xorPairUp, pairFanin]
  | [p] => by simp [xorPairUp, pairFanin_cons]
  | p :: q :: ps => by
      have ih := pairFanin_xorPairUp ps
      have hn := pairFanin_xorNode p q
      simp only [xorPairUp, pairFanin_cons]
      omega

/-- Repeatedly pair and XOR, `k` rounds at most.  The zero-fuel branch is unreachable for
`ps ≠ []`: every lemma about it, and `xorTree` itself, supply `ps.length ≤ k`. -/
private def xorFuel : ℕ → List (Circuit n × Circuit n) → Circuit n × Circuit n
  | 0, _ => (Circuit.node false [], Circuit.node true [])
  | _ + 1, [] => (Circuit.node false [], Circuit.node true [])
  | _ + 1, [p] => p
  | k + 1, p :: q :: ps => xorFuel k (xorPairUp (p :: q :: ps))

/-- The XOR tree computes the XOR, and its second component the negation. -/
private theorem xorFuel_eval (x : Fin n → Bool) :
    ∀ (k : ℕ) (ps : List (Circuit n × Circuit n)), ps.length ≤ k →
      (∀ p ∈ ps, IsDual x p) →
      (xorFuel k ps).1.eval x = xorAll x ps ∧ IsDual x (xorFuel k ps)
  | 0, [], _, _ => by
      refine ⟨?_, ?_⟩ <;> simp [xorFuel, xorAll, IsDual, Circuit.eval]
  | 0, _ :: _, h, _ => by simp at h
  | _ + 1, [], _, _ => by
      refine ⟨?_, ?_⟩ <;> simp [xorFuel, xorAll, IsDual, Circuit.eval]
  | _ + 1, [p], _, h => by
      refine ⟨?_, h p (by simp)⟩
      show p.1.eval x = _
      simp [xorAll]
  | k + 1, p :: q :: ps, h, hd => by
      have hp := length_xorPairUp (p :: q :: ps)
      have hlen : (xorPairUp (p :: q :: ps)).length ≤ k := by
        simp only [List.length_cons] at h hp ⊢; omega
      have ih := xorFuel_eval x k _ hlen (isDual_xorPairUp x _ hd)
      show ((xorFuel k (xorPairUp (p :: q :: ps))).1.eval x = _) ∧ _
      rw [ih.1, xorAll_xorPairUp x _ hd]
      exact ⟨rfl, ih.2⟩

/-- The XOR tree has depth `2⌈log₂ m⌉ + 2` over its leaves. -/
private theorem xorFuel_depth :
    ∀ (k : ℕ) (ps : List (Circuit n × Circuit n)), ps.length ≤ k →
      max (xorFuel k ps).1.depth (xorFuel k ps).2.depth
        ≤ pairDepth ps + 2 * Nat.clog 2 ps.length + 2
  | 0, [], _ => by simp [xorFuel, Circuit.depth_node, Circuit.maxDepth_nil, pairDepth]
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], _ => by simp [xorFuel, Circuit.depth_node, Circuit.maxDepth_nil, pairDepth]
  | _ + 1, [p], _ => by
      show max p.1.depth p.2.depth ≤ _
      rw [pairDepth_cons]
      simp [pairDepth]
  | k + 1, p :: q :: ps, h => by
      have hp := length_xorPairUp (p :: q :: ps)
      have hlen : (xorPairUp (p :: q :: ps)).length ≤ k := by
        simp only [List.length_cons] at h hp ⊢; omega
      have ih := xorFuel_depth k _ hlen
      have hd := pairDepth_xorPairUp (p :: q :: ps)
      have hclog : Nat.clog 2 (p :: q :: ps).length
          = Nat.clog 2 ((xorPairUp (p :: q :: ps)).length) + 1 := by
        rw [hp]
        have := Nat.clog_of_two_le (b := 2) (n := (p :: q :: ps).length)
          (by norm_num) (by simp)
        simpa using this
      show max (xorFuel k (xorPairUp (p :: q :: ps))).1.depth
        (xorFuel k (xorPairUp (p :: q :: ps))).2.depth ≤ _
      omega

/-- The XOR tree has fan-in 2. -/
private theorem xorFuel_fanin :
    ∀ (k : ℕ) (ps : List (Circuit n × Circuit n)), ps.length ≤ k →
      max (xorFuel k ps).1.maxFanin (xorFuel k ps).2.maxFanin ≤ max 2 (pairFanin ps)
  | 0, [], _ => by simp [xorFuel, Circuit.maxFanin_node, Circuit.maxFaninL_nil]
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], _ => by simp [xorFuel, Circuit.maxFanin_node, Circuit.maxFaninL_nil]
  | _ + 1, [p], _ => by
      show max p.1.maxFanin p.2.maxFanin ≤ _
      rw [pairFanin_cons]
      omega
  | k + 1, p :: q :: ps, h => by
      have hp := length_xorPairUp (p :: q :: ps)
      have hlen : (xorPairUp (p :: q :: ps)).length ≤ k := by
        simp only [List.length_cons] at h hp ⊢; omega
      have ih := xorFuel_fanin k _ hlen
      have hf := pairFanin_xorPairUp (p :: q :: ps)
      show max (xorFuel k (xorPairUp (p :: q :: ps))).1.maxFanin
        (xorFuel k (xorPairUp (p :: q :: ps))).2.maxFanin ≤ _
      omega

/-- The balanced XOR tree over a list of dual pairs. -/
private def xorTree (ps : List (Circuit n × Circuit n)) : Circuit n × Circuit n :=
  xorFuel ps.length ps

/-- The literal pairs `(xᵢ, ¬xᵢ)`, one per input bit. -/
private def parityPairs (m : ℕ) : List (Circuit m × Circuit m) :=
  (List.finRange m).map fun i => (Circuit.lit ⟨i, true⟩, Circuit.lit ⟨i, false⟩)

/-- Literal pairs are dual. -/
private theorem isDual_parityPairs (x : Fin n → Bool) :
    ∀ p ∈ parityPairs n, IsDual x p := by
  intro p hp
  simp only [parityPairs, List.mem_map] at hp
  obtain ⟨i, _, rfl⟩ := hp
  simp [IsDual, Circuit.eval, Lit.eval]

/-- Literal pairs have depth `0`. -/
private theorem pairDepth_parityPairs : pairDepth (parityPairs n) = 0 := by
  simp only [parityPairs]
  induction List.finRange n with
  | nil => rfl
  | cons i l ih => simp [pairDepth_cons, ih, Circuit.depth]

/-- Literal pairs have fan-in `0`. -/
private theorem pairFanin_parityPairs : pairFanin (parityPairs n) = 0 := by
  simp only [parityPairs]
  induction List.finRange n with
  | nil => rfl
  | cons i l ih => simp [pairFanin_cons, ih, Circuit.maxFanin]

/-- Literal pairs number one per input bit. -/
private theorem length_parityPairs : (parityPairs n).length = n := by
  simp [parityPairs]

/-- The XOR over literal pairs is the XOR of the input bits. -/
private theorem xorAll_parityPairs (x : Fin n → Bool) :
    xorAll x (parityPairs n)
      = (List.finRange n).foldr (fun i acc => Bool.xor (x i) acc) false := by
  simp only [parityPairs]
  induction List.finRange n with
  | nil => rfl
  | cons i l ih =>
      simp only [List.map_cons, xorAll_cons, List.foldr_cons, ih]
      simp [Circuit.eval, Lit.eval]

/-- The balanced binary XOR tree computing `PARITY` on `n` bits.  [AB09, Ex 6.26] -/
def parityCircuit (m : ℕ) : Circuit m := (xorTree (parityPairs m)).1

/-- `parityCircuit` computes the XOR of all input bits. -/
theorem parityCircuit_eval (x : Fin n → Bool) :
    (parityCircuit n).eval x
      = (List.finRange n).foldr (fun i acc => Bool.xor (x i) acc) false := by
  rw [parityCircuit, xorTree,
    (xorFuel_eval x _ (parityPairs n) (le_refl _) (isDual_parityPairs x)).1,
    xorAll_parityPairs]

/-- `parityCircuit` has fan-in `2`. -/
theorem parityCircuit_maxFanin_le : (parityCircuit n).maxFanin ≤ 2 := by
  have h := xorFuel_fanin (parityPairs n).length (parityPairs n) (le_refl _)
  rw [pairFanin_parityPairs] at h
  simp only [Nat.max_eq_left (Nat.zero_le 2)] at h
  exact le_trans (le_max_left _ _) h

/-- `parityCircuit` has depth `O(log n)`. -/
theorem parityCircuit_depth_le : (parityCircuit n).depth ≤ 4 * (Nat.log 2 n + 1) := by
  have h1 : (parityCircuit n).depth
      ≤ pairDepth (parityPairs n) + 2 * Nat.clog 2 (parityPairs n).length + 2 :=
    le_trans (le_max_left _ _)
      (xorFuel_depth (parityPairs n).length (parityPairs n) (le_refl _))
  rw [pairDepth_parityPairs, length_parityPairs] at h1
  have hc : Nat.clog 2 n ≤ Nat.log 2 n + 1 := by
    rw [Nat.clog_le_iff_le_pow (by norm_num)]
    exact Nat.le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) n)
  omega

/-- `parityCircuit` has polynomial size, by the depth bound and fan-in `2`. -/
theorem parityCircuit_size_le : (parityCircuit n).size ≤ 32 * (n + 1) ^ 4 := by
  have hd := parityCircuit_depth_le (n := n)
  have hs := Circuit.size_succ_le_two_pow (parityCircuit n) parityCircuit_maxFanin_le
  have hmono : (2 : ℕ) ^ ((parityCircuit n).depth + 1) ≤ 2 ^ (4 * (Nat.log 2 n + 1) + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlog : (2 : ℕ) ^ (Nat.log 2 n + 1) ≤ 2 * (n + 1) := by
    have := Nat.pow_log_le_add_one 2 n
    rw [pow_succ]
    omega
  have hfin : (2 : ℕ) ^ (4 * (Nat.log 2 n + 1) + 1) ≤ 32 * (n + 1) ^ 4 := by
    calc (2 : ℕ) ^ (4 * (Nat.log 2 n + 1) + 1)
        = 2 * (2 ^ (Nat.log 2 n + 1)) ^ 4 := by
          rw [pow_succ, ← pow_mul, Nat.mul_comm 4 (Nat.log 2 n + 1)]
          ring
      _ ≤ 2 * (2 * (n + 1)) ^ 4 := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hlog 4)
      _ = 32 * (n + 1) ^ 4 := by ring
  omega

/-- `PARITY` on the empty input is `false`. -/
theorem parityCircuit_eval_zero (x : Fin 0 → Bool) : (parityCircuit 0).eval x = false := by
  rw [parityCircuit_eval]; rfl

/-- `PARITY` on a one-bit input is that bit; note `Nat.log 2 1 = 0`, so the depth bound
`4 * (Nat.log 2 n + 1)` is the constant `4` here and at `n = 0`, not `0`. -/
theorem parityCircuit_eval_one (x : Fin 1 → Bool) : (parityCircuit 1).eval x = x 0 := by
  rw [parityCircuit_eval]; simp [List.finRange]

end BoolCircuit

/-- `PARITY = {x : x has an odd number of 1s}`.  [AB09, Ex 6.26] -/
def Language.parity : Language Bool := {w | w.count true % 2 = 1}

/-- `PARITY` membership is the iterated XOR of the word's letters. -/
theorem Language.mem_parity_iff (w : List Bool) :
    w ∈ Language.parity ↔ w.foldr Bool.xor false = true := by
  show w.count true % 2 = 1 ↔ _
  induction w with
  | nil => simp
  | cons b w ih =>
      cases b with
      | false => simpa [List.count_cons] using ih
      | true =>
          rcases Bool.eq_false_or_eq_true (w.foldr Bool.xor false) with hf | hf <;>
            rw [hf] at ih <;> simp_all <;> omega

/-- [AB09, Ex 6.26]: `PARITY ∈ NC¹`, via the balanced binary tree.

**Proof sketch.** `BoolCircuit.parityCircuit n` is the balanced binary tree whose leaves
are the `n` input bits and whose internal gates take the XOR of their two children.  Since
this circuit model negates only at literals, each node carries a *pair* — a circuit for the
XOR of its leaves and a circuit for its complement — and `xorNode` builds the pair for a
parent from those of its two children as `(a ∧ b') ∨ (a' ∧ b)` and `(a ∧ b) ∨ (a' ∧ b')`,
costing two levels of depth.  Halving the list `⌈log₂ n⌉` times therefore gives depth
`2⌈log₂ n⌉ + 2 ≤ 4(log₂ n + 1)` and fan-in `2`; polynomial size then follows from
`Circuit.size_succ_le_two_pow`, since a fan-in-2 tree of depth `d` has fewer than `2^(d+1)`
nodes.  Reading the tree at word length `|w|` and folding `List.finRange_map_get` gives the
XOR of `w`'s letters, which is `1` exactly when `w` has an odd number of `1`s. -/
theorem Language.parity_inNC_one : Language.parity.InNC 1 := by
  refine ⟨⟨BoolCircuit.parityCircuit⟩, fun n => BoolCircuit.parityCircuit_maxFanin_le,
    ⟨32, 4, fun n => BoolCircuit.parityCircuit_size_le⟩,
    ⟨4, fun n => by simpa using BoolCircuit.parityCircuit_depth_le⟩, ?_⟩
  ext w
  rw [BoolCircuit.TreeCircuitFamily.mem_language_iff, BoolCircuit.parityCircuit_eval,
    ← List.foldr_map, List.finRange_map_get, ← Language.mem_parity_iff]
