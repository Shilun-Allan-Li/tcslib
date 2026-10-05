/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Computability.Language
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Log
import TCSlib.Complexity.CircuitComplexity.Basic

/-!
# The formula classes `NC` and `AC`

The classes of [AB09, Defs 6.24 and 6.25] over tree circuits (formulas).  The book's
classes, over DAG circuits, are `Language.InNC` / `Language.InAC` in `NCAC.lean`, which also
compares the two.

## Main definitions

* `BoolCircuit.TreeCircuitFamily` — one `BoolCircuit.TreeCircuit n` per input length,
  with `language`, `IsPolySize`, `HasFaninTwo` and `HasPolylogDepth`.
* `Language.InTreeNC` — formula `NC^d`; `BoolCircuit.TreeNC` — `⋃_{i ≥ 1}`.
* `Language.InTreeAC` — formula `AC^d`; `BoolCircuit.TreeAC` — `⋃_{i ≥ 0}`.
* `BoolCircuit.TreeCircuit.toBinary` — rebuilds every unbounded gate as a balanced
  binary tree of gates of the same type.

## Main results

* `Language.InTreeNC.inTreeAC` and `Language.InTreeAC.inTreeNC_succ` — `NC^i ⊆ AC^i ⊆ NC^{i+1}`
  [AB09, p. 118], hence `BoolCircuit.TreeNC_eq_TreeAC`.
* `BoolCircuit.toBinary_eval`, `toBinary_maxFanin_le`, `toBinary_depth_le`,
  `toBinary_size_le` — the four facts that inclusion needs.

[AB09, Ex 6.26], `PARITY ∈ NC¹`, is in `TCSlib.Complexity.CircuitComplexity.Parity`.
The size, depth and fan-in arithmetic these proofs run on is in
`TCSlib.Complexity.CircuitComplexity.Basic`.

## Divergences from Arora–Barak §6.7.1

* **What is formalized.** `Language.InTreeNC d` and `Language.InTreeAC d` are AB's `NC^d` and
  `AC^d` taken over `BoolCircuit.TreeCircuit`, which is a *tree*: every gate feeds exactly
  one parent.  They are therefore AB's classes with fan-out restricted to `1` (formulas),
  where Def 6.1's circuits are DAGs.  AB's DAG classes are `Language.InNC` /
  `Language.InAC` (`NCAC.lean`).
* **Comparison with the DAG classes** (`NCAC.lean`).  Every formula class is inside the
  circuit class of the same level (`Language.InTreeNC.inNC`, `Language.InTreeAC.inAC`).
  Unfolding a fan-in-`f` DAG of depth `d` multiplies size by at most `(f + 1) ^ d`, so the
  two coincide where that stays polynomial: at `NC¹` (`Language.inNC_one_iff`) and `AC⁰`
  (`Language.inAC_zero_iff`).  The two indices differ, so the `NC` boundary must not be
  carried across to `AC`; above them no equality is known.
* **Size measure.** `IsPolySize` is AB's "poly(n) size", measured by `TreeCircuit.size`, which
  diverges from Def 6.1 in both directions.  It *lowers* the count by charging `1` for a
  `k`-ary gate where AB charges `k − 1` vertices — unbounded here, not a constant, since
  `AC^i` is the unbounded-fan-in class — and by not counting AB's `n` input vertices.  It
  *raises* the count by charging every literal occurrence a separate leaf, since a tree
  has no shared input vertices and no gate reuse.
* **Fan-in.** Bounded fan-in is the predicate `TreeCircuit.maxFanin ≤ 2` over the one
  unbounded-fan-in `TreeCircuit` type, not a separate inductive type — this is the idiom the
  LMN development already uses (`maxFanin ≤ w` as a hypothesis), and it lets
  `toBinary : TreeCircuit n → TreeCircuit n` be a plain function whose four properties are
  ordinary lemmas about one type.  `BoolCircuit.LayeredCircuit`, the layered DAG `LayeredPPoly.lean` uses,
  was rejected because `toBinary` recurses over a gate's child list, which it has not.
* **Basis.** `TreeCircuit` negates only at literals, so a `NOT` gate is free and contributes
  no depth, where AB's Def 6.1 basis `{∧, ∨, ¬}` charges one for it.
* **`O(log^d n)`.** Written `∃ b, ∀ n, depth ≤ b * (Nat.log 2 n + 1) ^ d`, the shape
  `LayeredPPoly.lean` uses for size.  The `+ 1` repairs the same degeneracy: `Nat.log 2 n = 0`
  for `n ≤ 1`, so `b * (Nat.log 2 n) ^ d` would force depth `0` at those lengths.
* **`NC ⊆ P/poly`** is proved for the DAG classes (`BoolCircuit.NC_subset_PPoly`), and
  reaches these through `Language.InTreeNC.inNC`.
* **Uniformity.** AB's "one can also define uniform `NC`" needs logspace and is out of
  scope for now (no logspace machinery).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

variable {n : ℕ}

/-! ### Circuit families -/

/-- A non-uniform family of Boolean circuits, one per input length. -/
structure TreeCircuitFamily where
  /-- The circuit handling inputs of length `n`. -/
  circuit : (n : ℕ) → TreeCircuit n

namespace TreeCircuitFamily

variable (C : TreeCircuitFamily)

/-- The family accepts `w` when the circuit for length `w.length` outputs `true`. -/
def Accepts (w : List Bool) : Prop :=
  (C.circuit w.length).eval w.get = true

/-- The language decided by the family. -/
def language : Language Bool :=
  {w | C.Accepts w}

/-- Membership in the decided language, unfolded to the circuit's output. -/
@[simp]
theorem mem_language_iff (w : List Bool) :
    w ∈ C.language ↔ (C.circuit w.length).eval w.get = true :=
  Iff.rfl

/-- The family has polynomial size. -/
def IsPolySize : Prop :=
  ∃ a k : ℕ, ∀ n, (C.circuit n).size ≤ a * (n + 1) ^ k

/-- Every gate of every circuit in the family has at most two inputs. -/
def HasFaninTwo : Prop :=
  ∀ n, (C.circuit n).maxFanin ≤ 2

/-- The family has polylogarithmic depth `O(log^d n)` (constant depth when `d = 0`). -/
def HasPolylogDepth (d : ℕ) : Prop :=
  ∃ b : ℕ, ∀ n, (C.circuit n).depth ≤ b * (Nat.log 2 n + 1) ^ d

end TreeCircuitFamily

end BoolCircuit

/-- `L ∈ NC^d`: a polynomial-size fan-in-2 family of depth `O(log^d n)` decides `L`.
[AB09, Def 6.24] -/
def Language.InTreeNC (d : ℕ) (L : Language Bool) : Prop :=
  ∃ C : BoolCircuit.TreeCircuitFamily,
    C.HasFaninTwo ∧ C.IsPolySize ∧ C.HasPolylogDepth d ∧ C.language = L

/-- `L ∈ AC^d`: as `NC^d`, but gates may have unbounded fan-in.  [AB09, Def 6.25] -/
def Language.InTreeAC (d : ℕ) (L : Language Bool) : Prop :=
  ∃ C : BoolCircuit.TreeCircuitFamily,
    C.IsPolySize ∧ C.HasPolylogDepth d ∧ C.language = L

namespace BoolCircuit

/-- `NC^d` as a set of languages. -/
def TreeNCLevel (d : ℕ) : Set (Language Bool) := {L | L.InTreeNC d}

/-- `AC^d` as a set of languages. -/
def TreeACLevel (d : ℕ) : Set (Language Bool) := {L | L.InTreeAC d}

/-- `NC = ⋃_{i ≥ 1} NC^i`.  [AB09, Def 6.24] -/
def TreeNC : Set (Language Bool) := ⋃ i ∈ Set.Ici 1, TreeNCLevel i

/-- `AC = ⋃_{i ≥ 0} AC^i`.  [AB09, Def 6.25] -/
def TreeAC : Set (Language Bool) := ⋃ i, TreeACLevel i

/-- Membership in `NC` is membership in some `NC^i` with `i ≥ 1`. -/
theorem mem_TreeNC_iff (L : Language Bool) : L ∈ TreeNC ↔ ∃ i, 1 ≤ i ∧ L.InTreeNC i := by
  simp [TreeNC, TreeNCLevel, Set.mem_iUnion]

/-- Membership in `AC` is membership in some `AC^i`. -/
theorem mem_TreeAC_iff (L : Language Bool) : L ∈ TreeAC ↔ ∃ i, L.InTreeAC i := by
  simp [TreeAC, TreeACLevel, Set.mem_iUnion]

end BoolCircuit

/-- `NC^i ⊆ AC^i`: forget the fan-in bound.  [AB09, p. 118] -/
theorem Language.InTreeNC.inTreeAC {d : ℕ} {L : Language Bool} (h : L.InTreeNC d) : L.InTreeAC d := by
  obtain ⟨C, _, hs, hd, hl⟩ := h
  exact ⟨C, hs, hd, hl⟩

namespace BoolCircuit

variable {n : ℕ}

/-! ### Simulating an unbounded gate by a balanced binary tree -/

/-- Pair adjacent children under a gate of type `b`, halving the list. -/
private def pairUp (b : Bool) : List (TreeCircuit n) → List (TreeCircuit n)
  | [] => []
  | [c] => [c]
  | c₁ :: c₂ :: cs => TreeCircuit.node b [c₁, c₂] :: pairUp b cs

/-- Pairing halves the list, rounding up. -/
private theorem length_pairUp (b : Bool) :
    ∀ cs : List (TreeCircuit n), (pairUp b cs).length = (cs.length + 1) / 2
  | [] => by simp [pairUp]
  | [_] => by simp [pairUp]
  | _ :: _ :: cs => by
      have := length_pairUp b cs
      simp only [pairUp, List.length_cons] at *
      omega

/-- Pairing preserves the value of the surrounding gate. -/
private theorem eval_node_pairUp (b : Bool) (x : Fin n → Bool) :
    ∀ cs : List (TreeCircuit n),
      (TreeCircuit.node b (pairUp b cs)).eval x = (TreeCircuit.node b cs).eval x
  | [] => rfl
  | [_] => by cases b <;> simp [pairUp, TreeCircuit.eval]
  | c₁ :: c₂ :: cs => by
      have := eval_node_pairUp b x cs
      cases b <;>
        simp only [pairUp, TreeCircuit.eval, List.foldr_cons, List.foldr_nil] at * <;>
        simp [this, Bool.and_assoc, Bool.or_assoc]

/-- Pairing adds at most one to the depth. -/
private theorem maxDepth_pairUp (b : Bool) :
    ∀ cs : List (TreeCircuit n), TreeCircuit.maxDepth (pairUp b cs) ≤ 1 + TreeCircuit.maxDepth cs
  | [] => by simp [pairUp, TreeCircuit.maxDepth_nil]
  | [c] => by simp [pairUp]
  | c₁ :: c₂ :: cs => by
      have ih := maxDepth_pairUp b cs
      have h1 : (TreeCircuit.node b [c₁, c₂]).depth
          = 1 + max c₁.depth (max c₂.depth 0) := by
        rw [TreeCircuit.depth_node, TreeCircuit.maxDepth_cons, TreeCircuit.maxDepth_cons, TreeCircuit.maxDepth_nil]
      simp only [pairUp, TreeCircuit.maxDepth_cons, h1]
      omega

/-- Pairing does not increase the total size plus length. -/
private theorem sumSize_pairUp (b : Bool) :
    ∀ cs : List (TreeCircuit n),
      TreeCircuit.sumSize (pairUp b cs) + (pairUp b cs).length ≤
        TreeCircuit.sumSize cs + cs.length
  | [] => le_refl 0
  | [_] => le_refl _
  | c₁ :: c₂ :: cs => by
      have ih := sumSize_pairUp b cs
      have h1 : (TreeCircuit.node b [c₁, c₂]).size = 1 + (c₁.size + (c₂.size + 0)) := by
        rw [TreeCircuit.size_node, TreeCircuit.sumSize_cons, TreeCircuit.sumSize_cons, TreeCircuit.sumSize_nil]
      simp only [pairUp, TreeCircuit.sumSize_cons, h1, List.length_cons]
      omega

/-- Pairing introduces only fan-in-2 gates. -/
private theorem maxFaninL_pairUp (b : Bool) :
    ∀ cs : List (TreeCircuit n), TreeCircuit.maxFaninL (pairUp b cs) ≤ max 2 (TreeCircuit.maxFaninL cs)
  | [] => Nat.zero_le _
  | [c] => by simp [pairUp, TreeCircuit.maxFaninL_cons, TreeCircuit.maxFaninL_nil]
  | c₁ :: c₂ :: cs => by
      have ih := maxFaninL_pairUp b cs
      have h1 : (TreeCircuit.node b [c₁, c₂]).maxFanin
          = max 2 (max c₁.maxFanin (max c₂.maxFanin 0)) := by
        rw [TreeCircuit.maxFanin_node, TreeCircuit.maxFaninL_cons, TreeCircuit.maxFaninL_cons,
          TreeCircuit.maxFaninL_nil]
        norm_num
      simp only [pairUp, TreeCircuit.maxFaninL_cons, h1]
      omega

/-- Repeatedly pair a child list, `k` rounds at most, into a single circuit. -/
private def combineFuel (b : Bool) : ℕ → List (TreeCircuit n) → TreeCircuit n
  | 0, cs => TreeCircuit.node b cs
  | _ + 1, [] => TreeCircuit.node b []
  | _ + 1, [c] => c
  | k + 1, c₁ :: c₂ :: cs => combineFuel b k (pairUp b (c₁ :: c₂ :: cs))

/-- Combine a child list into a balanced binary tree of gates of type `b`. -/
private def combine (b : Bool) (cs : List (TreeCircuit n)) : TreeCircuit n :=
  combineFuel b cs.length cs

/-- Combining computes the same value as the unbounded gate. -/
private theorem combineFuel_eval (b : Bool) (x : Fin n → Bool) :
    ∀ (k : ℕ) (cs : List (TreeCircuit n)),
      (combineFuel b k cs).eval x = (TreeCircuit.node b cs).eval x
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | _ + 1, [c] => by cases b <;> simp [combineFuel, TreeCircuit.eval]
  | k + 1, c₁ :: c₂ :: cs => by
      show (combineFuel b k (pairUp b (c₁ :: c₂ :: cs))).eval x = _
      rw [combineFuel_eval b x k, eval_node_pairUp]

/-- Combining produces only fan-in-2 gates, given enough rounds. -/
private theorem combineFuel_maxFanin (b : Bool) :
    ∀ (k : ℕ) (cs : List (TreeCircuit n)), cs.length ≤ k →
      (combineFuel b k cs).maxFanin ≤ max 2 (TreeCircuit.maxFaninL cs)
  | 0, [], _ => by simp [combineFuel, TreeCircuit.maxFanin_node, TreeCircuit.maxFaninL_nil]
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], _ => by simp [combineFuel, TreeCircuit.maxFanin_node, TreeCircuit.maxFaninL_nil]
  | _ + 1, [c], _ => by
      show c.maxFanin ≤ _
      rw [TreeCircuit.maxFaninL_cons, TreeCircuit.maxFaninL_nil]
      omega
  | k + 1, c₁ :: c₂ :: cs, h => by
      have hp := length_pairUp b (c₁ :: c₂ :: cs)
      have hlen : (pairUp b (c₁ :: c₂ :: cs)).length ≤ k := by
        simp only [List.length_cons] at h hp ⊢; omega
      have ih := combineFuel_maxFanin b k _ hlen
      have h2 := maxFaninL_pairUp b (c₁ :: c₂ :: cs)
      show (combineFuel b k (pairUp b (c₁ :: c₂ :: cs))).maxFanin ≤ _
      omega

/-- Combining `m` children costs `⌈log₂ m⌉` extra levels of depth. -/
private theorem combineFuel_depth (b : Bool) :
    ∀ (k : ℕ) (cs : List (TreeCircuit n)), cs.length ≤ k →
      (combineFuel b k cs).depth ≤ TreeCircuit.maxDepth cs + Nat.clog 2 cs.length + 1
  | 0, [], _ => by simp [combineFuel, TreeCircuit.depth_node, TreeCircuit.maxDepth_nil]
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], _ => by simp [combineFuel, TreeCircuit.depth_node, TreeCircuit.maxDepth_nil]
  | _ + 1, [c], _ => by
      show c.depth ≤ _
      rw [TreeCircuit.maxDepth_cons, TreeCircuit.maxDepth_nil]
      simp
  | k + 1, c₁ :: c₂ :: cs, h => by
      have hp := length_pairUp b (c₁ :: c₂ :: cs)
      have hlen : (pairUp b (c₁ :: c₂ :: cs)).length ≤ k := by
        simp only [List.length_cons] at h hp ⊢; omega
      have ih := combineFuel_depth b k _ hlen
      have h2 := maxDepth_pairUp b (c₁ :: c₂ :: cs)
      have hclog : Nat.clog 2 (c₁ :: c₂ :: cs).length
          = Nat.clog 2 ((pairUp b (c₁ :: c₂ :: cs)).length) + 1 := by
        rw [hp]
        have := Nat.clog_of_two_le (b := 2) (n := (c₁ :: c₂ :: cs).length)
          (by norm_num) (by simp)
        simpa using this
      show (combineFuel b k (pairUp b (c₁ :: c₂ :: cs))).depth ≤ _
      omega

/-- Combining `m` children costs at most `m` extra gates. -/
private theorem combineFuel_size (b : Bool) :
    ∀ (k : ℕ) (cs : List (TreeCircuit n)),
      (combineFuel b k cs).size ≤ TreeCircuit.sumSize cs + cs.length + 1
  | 0, cs => by show (TreeCircuit.node b cs).size ≤ _; rw [TreeCircuit.size_node]; omega
  | _ + 1, [] => by simp [combineFuel, TreeCircuit.size_node, TreeCircuit.sumSize_nil]
  | _ + 1, [c] => by show c.size ≤ _; rw [TreeCircuit.sumSize_cons, TreeCircuit.sumSize_nil]; omega
  | k + 1, c₁ :: c₂ :: cs => by
      have ih := combineFuel_size b k (pairUp b (c₁ :: c₂ :: cs))
      have h2 := sumSize_pairUp b (c₁ :: c₂ :: cs)
      show (combineFuel b k (pairUp b (c₁ :: c₂ :: cs))).size ≤ _
      omega

/-- `combine` computes the unbounded gate. -/
private theorem combine_eval (b : Bool) (cs : List (TreeCircuit n)) (x : Fin n → Bool) :
    (combine b cs).eval x = (TreeCircuit.node b cs).eval x :=
  combineFuel_eval b x _ cs

/-- `combine` has fan-in 2, unless a child already had more. -/
private theorem combine_maxFanin (b : Bool) (cs : List (TreeCircuit n)) :
    (combine b cs).maxFanin ≤ max 2 (TreeCircuit.maxFaninL cs) :=
  combineFuel_maxFanin b _ cs (le_refl _)

/-- `combine` adds `⌈log₂ |cs|⌉ + 1` to the children's depth. -/
private theorem combine_depth (b : Bool) (cs : List (TreeCircuit n)) :
    (combine b cs).depth ≤ TreeCircuit.maxDepth cs + Nat.clog 2 cs.length + 1 :=
  combineFuel_depth b _ cs (le_refl _)

/-- `combine` adds `|cs| + 1` to the children's total size. -/
private theorem combine_size (b : Bool) (cs : List (TreeCircuit n)) :
    (combine b cs).size ≤ TreeCircuit.sumSize cs + cs.length + 1 :=
  combineFuel_size b _ cs

/-- Rebuild every gate of a circuit as a balanced binary tree of gates of the same
type, so that the result has fan-in `2`.  [AB09, p. 118] -/
def TreeCircuit.toBinary : TreeCircuit n → TreeCircuit n
  | .lit l => .lit l
  | .node b cs => combine b (cs.map TreeCircuit.toBinary)

/-- A gate's value is unchanged when its children are replaced by equivalent ones. -/
private theorem eval_node_map (b : Bool) (x : Fin n → Bool) (f : TreeCircuit n → TreeCircuit n) :
    ∀ cs : List (TreeCircuit n), (∀ c ∈ cs, (f c).eval x = c.eval x) →
      (TreeCircuit.node b (cs.map f)).eval x = (TreeCircuit.node b cs).eval x
  | [], _ => rfl
  | c :: cs, h => by
      have ih := eval_node_map b x f cs (fun d hd => h d (List.mem_cons_of_mem _ hd))
      have hc := h c (List.mem_cons_self ..)
      cases b <;>
        simp only [List.map_cons, TreeCircuit.eval, List.foldr_cons] at ih ⊢ <;>
        rw [hc, ih]

/-- A depth bound on every image element bounds the image's depth. -/
private theorem maxDepth_map_le (f : TreeCircuit n → TreeCircuit n) (m : ℕ) :
    ∀ cs : List (TreeCircuit n), (∀ c ∈ cs, (f c).depth ≤ m) →
      TreeCircuit.maxDepth (cs.map f) ≤ m
  | [], _ => Nat.zero_le _
  | c :: cs, h => by
      have ih := maxDepth_map_le f m cs (fun d hd => h d (List.mem_cons_of_mem _ hd))
      have hc := h c (List.mem_cons_self ..)
      simp only [List.map_cons, TreeCircuit.maxDepth_cons]
      omega

/-- A fan-in bound on every image element bounds the image's fan-in. -/
private theorem maxFaninL_map_le (f : TreeCircuit n → TreeCircuit n) (m : ℕ) :
    ∀ cs : List (TreeCircuit n), (∀ c ∈ cs, (f c).maxFanin ≤ m) →
      TreeCircuit.maxFaninL (cs.map f) ≤ m
  | [], _ => Nat.zero_le _
  | c :: cs, h => by
      have ih := maxFaninL_map_le f m cs (fun d hd => h d (List.mem_cons_of_mem _ hd))
      have hc := h c (List.mem_cons_self ..)
      simp only [List.map_cons, TreeCircuit.maxFaninL_cons]
      omega

/-- `toBinary` computes the same function. -/
theorem toBinary_eval : ∀ (c : TreeCircuit n) (x : Fin n → Bool), c.toBinary.eval x = c.eval x := by
  intro c
  induction c using TreeCircuit.ind with
  | hlit l => intro x; simp only [TreeCircuit.toBinary]
  | hnode b cs ih =>
      intro x
      simp only [TreeCircuit.toBinary]
      rw [combine_eval]
      exact eval_node_map b x TreeCircuit.toBinary cs (fun c hc => ih c hc x)

/-- `toBinary` produces a fan-in-2 circuit. -/
theorem toBinary_maxFanin_le : ∀ c : TreeCircuit n, c.toBinary.maxFanin ≤ 2 := by
  intro c
  induction c using TreeCircuit.ind with
  | hlit l => simp [TreeCircuit.toBinary, TreeCircuit.maxFanin]
  | hnode b cs ih =>
      simp only [TreeCircuit.toBinary]
      have h1 := combine_maxFanin b (cs.map TreeCircuit.toBinary)
      have h2 := maxFaninL_map_le TreeCircuit.toBinary 2 cs ih
      omega

/-- The list form of `toBinary_size_le`, in the strengthened form the induction needs. -/
private theorem sumSize_map_toBinary :
    ∀ cs : List (TreeCircuit n), (∀ c ∈ cs, c.toBinary.size + 1 ≤ 3 * c.size) →
      TreeCircuit.sumSize (cs.map TreeCircuit.toBinary) + cs.length ≤ 3 * TreeCircuit.sumSize cs
  | [], _ => by simp [TreeCircuit.sumSize_nil]
  | c :: cs, h => by
      have ih := sumSize_map_toBinary cs (fun d hd => h d (List.mem_cons_of_mem _ hd))
      have hc := h c (List.mem_cons_self ..)
      simp only [List.map_cons, TreeCircuit.sumSize_cons, List.length_cons]
      omega

/-- `toBinary` at most triples the size, with one unit to spare. -/
private theorem toBinary_size_succ_le : ∀ c : TreeCircuit n, c.toBinary.size + 1 ≤ 3 * c.size := by
  intro c
  induction c using TreeCircuit.ind with
  | hlit l => simp [TreeCircuit.toBinary, TreeCircuit.size]
  | hnode b cs ih =>
      simp only [TreeCircuit.toBinary]
      have h1 := combine_size b (cs.map TreeCircuit.toBinary)
      have h2 := sumSize_map_toBinary cs ih
      rw [TreeCircuit.size_node]
      simp only [List.length_map] at h1
      omega

/-- `toBinary` at most triples the size. -/
theorem toBinary_size_le (c : TreeCircuit n) : c.toBinary.size ≤ 3 * c.size :=
  le_trans (Nat.le_succ _) (toBinary_size_succ_le c)

/-- `toBinary` multiplies the depth by `⌈log₂ w⌉ + 1`, where `w` bounds the fan-in. -/
theorem toBinary_depth_le {w : ℕ} : ∀ c : TreeCircuit n, c.maxFanin ≤ w →
    c.toBinary.depth ≤ c.depth * (Nat.clog 2 w + 1) := by
  intro c
  induction c using TreeCircuit.ind with
  | hlit l => intro _; simp [TreeCircuit.toBinary, TreeCircuit.depth]
  | hnode b cs ih =>
      intro h
      rw [TreeCircuit.maxFanin_node] at h
      have hlen : cs.length ≤ w := le_trans (le_max_left _ _) h
      have hfan : TreeCircuit.maxFaninL cs ≤ w := le_trans (le_max_right _ _) h
      have hB : TreeCircuit.maxDepth (cs.map TreeCircuit.toBinary)
          ≤ TreeCircuit.maxDepth cs * (Nat.clog 2 w + 1) :=
        maxDepth_map_le _ _ cs fun c hc =>
          le_trans (ih c hc (le_trans (TreeCircuit.maxFanin_le_maxFaninL hc) hfan))
            (Nat.mul_le_mul_right _ (TreeCircuit.depth_le_maxDepth hc))
      have hC : Nat.clog 2 cs.length ≤ Nat.clog 2 w := Nat.clog_mono_right 2 hlen
      simp only [TreeCircuit.toBinary]
      refine le_trans (combine_depth b (cs.map TreeCircuit.toBinary)) ?_
      rw [TreeCircuit.depth_node, Nat.add_mul, Nat.one_mul, List.length_map]
      omega

/-- `⌈log₂⌉` of a polynomial is `O(log n)`. -/
theorem clog_poly_le (a k m : ℕ) :
    Nat.clog 2 (a * (m + 1) ^ k) ≤ a + k * (Nat.log 2 m + 1) := by
  rw [Nat.clog_le_iff_le_pow (by norm_num)]
  calc a * (m + 1) ^ k
      ≤ 2 ^ a * (2 ^ (Nat.log 2 m + 1)) ^ k :=
        Nat.mul_le_mul (Nat.le_of_lt a.lt_two_pow_self)
          (Nat.pow_le_pow_left (Nat.lt_pow_succ_log_self (by norm_num) m) k)
    _ = 2 ^ (a + k * (Nat.log 2 m + 1)) := by
        rw [← pow_mul, ← pow_add, Nat.mul_comm (Nat.log 2 m + 1) k]

end BoolCircuit

/-- `AC^i ⊆ NC^{i+1}`: rebuild every unbounded gate as a tree of fan-in-2 gates, which
costs a factor `O(log n)` in depth because the fan-in is at most the size, hence
`poly(n)`.  [AB09, p. 118]

**Proof sketch.** Let `{Cₙ}` decide `L` with `|Cₙ| ≤ a(n+1)ᵏ` and `depth Cₙ ≤ b(log n+1)ⁱ`.
A gate's fan-in never exceeds the circuit's size, so every gate of `Cₙ` has at most
`w = a(n+1)ᵏ` children, and `⌈log₂ w⌉ + 1 ≤ (a+k+1)(log n + 1)`.  Replacing each gate by
`TreeCircuit.toBinary`'s balanced binary tree of gates of the same type multiplies the depth by
`⌈log₂ w⌉ + 1`, so the new depth is at most `b(a+k+1)(log n+1)^{i+1}`; it at most triples
the size, so the family is still polynomial; it has fan-in `2`; and it computes the same
function, so it decides the same language. -/
theorem Language.InTreeAC.inTreeNC_succ {d : ℕ} {L : Language Bool} (h : L.InTreeAC d) :
    L.InTreeNC (d + 1) := by
  classical
  obtain ⟨C, ⟨a, k, hsize⟩, ⟨b, hdepth⟩, hlang⟩ := h
  refine ⟨⟨fun n => (C.circuit n).toBinary⟩, fun n => BoolCircuit.toBinary_maxFanin_le _,
    ⟨3 * a, k, fun n => ?_⟩, ⟨b * (a + k + 1), fun n => ?_⟩, ?_⟩
  · calc ((C.circuit n).toBinary).size
        ≤ 3 * (C.circuit n).size := BoolCircuit.toBinary_size_le _
      _ ≤ 3 * (a * (n + 1) ^ k) := Nat.mul_le_mul_left 3 (hsize n)
      _ = 3 * a * (n + 1) ^ k := (Nat.mul_assoc 3 a _).symm
  · have hfan : (C.circuit n).maxFanin ≤ a * (n + 1) ^ k :=
      le_trans (BoolCircuit.TreeCircuit.maxFanin_le_size _) (hsize n)
    have hK : Nat.clog 2 (a * (n + 1) ^ k) + 1 ≤ (a + k + 1) * (Nat.log 2 n + 1) := by
      have hpoly := BoolCircuit.clog_poly_le a k n
      have e1 : a ≤ a * (Nat.log 2 n + 1) := Nat.le_mul_of_pos_right a (by omega)
      have e2 : (a + k + 1) * (Nat.log 2 n + 1)
          = a * (Nat.log 2 n + 1) + k * (Nat.log 2 n + 1) + (Nat.log 2 n + 1) := by ring
      omega
    calc ((C.circuit n).toBinary).depth
        ≤ (C.circuit n).depth * (Nat.clog 2 (a * (n + 1) ^ k) + 1) :=
          BoolCircuit.toBinary_depth_le _ hfan
      _ ≤ (b * (Nat.log 2 n + 1) ^ d) * ((a + k + 1) * (Nat.log 2 n + 1)) :=
          Nat.mul_le_mul (hdepth n) hK
      _ = b * (a + k + 1) * (Nat.log 2 n + 1) ^ (d + 1) := by ring
  · rw [← hlang]
    ext w
    simp [BoolCircuit.TreeCircuitFamily.mem_language_iff, BoolCircuit.toBinary_eval]

namespace BoolCircuit

/-- `NC^i ⊆ AC^i`.  [AB09, p. 118] -/
theorem TreeNCLevel_subset_ACLevel (i : ℕ) : TreeNCLevel i ⊆ TreeACLevel i :=
  fun _ h => Language.InTreeNC.inTreeAC h

/-- `AC^i ⊆ NC^{i+1}`.  [AB09, p. 118] -/
theorem TreeACLevel_subset_NCLevel_succ (i : ℕ) : TreeACLevel i ⊆ TreeNCLevel (i + 1) :=
  fun _ h => Language.InTreeAC.inTreeNC_succ h

/-- The two inclusions make the **unions** coincide: `NC = AC` — no levelwise
equality is asserted — a corollary of [AB09, p. 118], which states the
inclusions only. -/
theorem TreeNC_eq_TreeAC : TreeNC = TreeAC := by
  ext L
  rw [mem_TreeNC_iff, mem_TreeAC_iff]
  constructor
  · rintro ⟨i, _, hi⟩
    exact ⟨i, hi.inTreeAC⟩
  · rintro ⟨i, hi⟩
    exact ⟨i + 1, Nat.le_add_left 1 i, hi.inTreeNC_succ⟩

end BoolCircuit
