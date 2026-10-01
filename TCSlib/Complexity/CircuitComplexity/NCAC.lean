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
# The circuit classes `NC` and `AC`

## Main definitions

* `BoolCircuit.TreeCircuitFamily` — one `BoolCircuit.Circuit n` per input length,
  with `language`, `IsPolySize`, `HasFaninTwo` and `HasLogDepth`.
* `Language.InNC` — [AB09, Def 6.24], `NC^d`; `BoolCircuit.NC` — `⋃_{i ≥ 1} NC^i`.
* `Language.InAC` — [AB09, Def 6.25], `AC^d`; `BoolCircuit.AC` — `⋃_{i ≥ 0} AC^i`.
* `BoolCircuit.Circuit.toBinary` — rebuilds every unbounded gate as a balanced
  binary tree of gates of the same type.

## Main results

* `Language.InNC.inAC` and `Language.InAC.inNC_succ` — `NC^i ⊆ AC^i ⊆ NC^{i+1}`
  [AB09, p. 118], hence `BoolCircuit.NC_eq_AC`.
* `BoolCircuit.toBinary_eval`, `toBinary_maxFanin_le`, `toBinary_depth_le`,
  `toBinary_size_le` — the four facts that inclusion needs.

[AB09, Ex 6.26], `PARITY ∈ NC¹`, is in `TCSlib.Complexity.CircuitComplexity.Parity`.
The size, depth and fan-in arithmetic these proofs run on is in
`TCSlib.Complexity.CircuitComplexity.Basic`.

## Divergences from Arora–Barak §6.7.1

* **What is formalized.** `Language.InNC d` and `Language.InAC d` are AB's `NC^d` and
  `AC^d` taken over `BoolCircuit.Circuit`, which is a *tree*: every gate feeds exactly
  one parent.  They are therefore AB's classes with fan-out restricted to `1` (formulas),
  where Def 6.1's circuits are DAGs.  AB's DAG classes are not defined anywhere in this
  development, and **no comparison between them and these is formalized**.  The next
  bullet describes the gap to AB; it is not a theorem of anything below.
* **Informal expectation, not proved here.** Unfolding a fan-in-`f` DAG of depth `d` into
  a tree duplicates a node once per consumer, blowing the node count up by a factor of at
  most `f ^ d`, so the fan-out-1 restriction is expected to be harmless exactly where a
  polynomial-size family stays polynomial: on the `NC` side at `i = 1` (`f = 2`,
  `d = O(log n)`), and on the `AC` side at `i = 0` (`f = poly(n)`, `d = O(1)`).  The two
  indices differ, so the `NC` boundary must not be carried across to `AC`.  Neither AB's
  DAG classes nor this unfolding is formalized, so
  **neither expectation is a theorem of this development**;
  `Circuit.size_succ_le_two_pow` (`Basic.lean`) proves only the tree-side bound.
* **Size measure.** `IsPolySize` is AB's "poly(n) size", measured by `Circuit.size`, which
  diverges from Def 6.1 in both directions.  It *lowers* the count by charging `1` for a
  `k`-ary gate where AB charges `k − 1` vertices — unbounded here, not a constant, since
  `AC^i` is the unbounded-fan-in class — and by not counting AB's `n` input vertices.  It
  *raises* the count by charging every literal occurrence a separate leaf, since a tree
  has no shared input vertices and no gate reuse.
* **Fan-in.** Bounded fan-in is the predicate `Circuit.maxFanin ≤ 2` over the one
  unbounded-fan-in `Circuit` type, not a separate inductive type — this is the idiom the
  LMN development already uses (`maxFanin ≤ w` as a hypothesis), and it lets
  `toBinary : Circuit n → Circuit n` be a plain function whose four properties are
  ordinary lemmas about one type.  `ACP.FeedForward`, the layered DAG `PPoly.lean` uses,
  was rejected because `toBinary` recurses over a gate's child list, which it has not.
* **Basis.** `Circuit` negates only at literals, so a `NOT` gate is free and contributes
  no depth, where AB's Def 6.1 basis `{∧, ∨, ¬}` charges one for it.
* **`O(log^d n)`.** Written `∃ b, ∀ n, depth ≤ b * (Nat.log 2 n + 1) ^ d`, the shape
  `PPoly.lean` uses for size.  The `+ 1` repairs the same degeneracy: `Nat.log 2 n = 0`
  for `n ≤ 1`, so `b * (Nat.log 2 n) ^ d` would force depth `0` at those lengths.
* **`NC ⊆ P/poly`.** Statable — `BoolCircuit.NC` and `ACP.PPoly` are both
  `Set (Language Bool)` — but not provable here: there is no bridge from
  `BoolCircuit.Circuit` to `ACP.CircuitFamily` (`ch6/PLAN.md`, deferred follow-ups).
* **Uniformity.** AB's "one can also define uniform `NC`" needs logspace and is out of
  scope; see `ch6/NOT_FORMALIZED.md`.

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
  circuit : (n : ℕ) → Circuit n

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

/-- The family has depth `O(log^d n)`. -/
def HasLogDepth (d : ℕ) : Prop :=
  ∃ b : ℕ, ∀ n, (C.circuit n).depth ≤ b * (Nat.log 2 n + 1) ^ d

end TreeCircuitFamily

end BoolCircuit

/-- `L ∈ NC^d`: a polynomial-size fan-in-2 family of depth `O(log^d n)` decides `L`.
[AB09, Def 6.24] -/
def Language.InNC (d : ℕ) (L : Language Bool) : Prop :=
  ∃ C : BoolCircuit.TreeCircuitFamily,
    C.HasFaninTwo ∧ C.IsPolySize ∧ C.HasLogDepth d ∧ C.language = L

/-- `L ∈ AC^d`: as `NC^d`, but gates may have unbounded fan-in.  [AB09, Def 6.25] -/
def Language.InAC (d : ℕ) (L : Language Bool) : Prop :=
  ∃ C : BoolCircuit.TreeCircuitFamily,
    C.IsPolySize ∧ C.HasLogDepth d ∧ C.language = L

namespace BoolCircuit

/-- `NC^d` as a set of languages. -/
def NCLevel (d : ℕ) : Set (Language Bool) := {L | L.InNC d}

/-- `AC^d` as a set of languages. -/
def ACLevel (d : ℕ) : Set (Language Bool) := {L | L.InAC d}

/-- `NC = ⋃_{i ≥ 1} NC^i`.  [AB09, Def 6.24] -/
def NC : Set (Language Bool) := ⋃ i ∈ Set.Ici 1, NCLevel i

/-- `AC = ⋃_{i ≥ 0} AC^i`.  [AB09, Def 6.25] -/
def AC : Set (Language Bool) := ⋃ i, ACLevel i

/-- Membership in `NC` is membership in some `NC^i` with `i ≥ 1`. -/
theorem mem_NC_iff (L : Language Bool) : L ∈ NC ↔ ∃ i, 1 ≤ i ∧ L.InNC i := by
  simp [NC, NCLevel, Set.mem_iUnion]

/-- Membership in `AC` is membership in some `AC^i`. -/
theorem mem_AC_iff (L : Language Bool) : L ∈ AC ↔ ∃ i, L.InAC i := by
  simp [AC, ACLevel, Set.mem_iUnion]

end BoolCircuit

/-- `NC^i ⊆ AC^i`: forget the fan-in bound.  [AB09, p. 118] -/
theorem Language.InNC.inAC {d : ℕ} {L : Language Bool} (h : L.InNC d) : L.InAC d := by
  obtain ⟨C, _, hs, hd, hl⟩ := h
  exact ⟨C, hs, hd, hl⟩

namespace BoolCircuit

variable {n : ℕ}

/-! ### Simulating an unbounded gate by a balanced binary tree -/

/-- Pair adjacent children under a gate of type `b`, halving the list. -/
private def pairUp (b : Bool) : List (Circuit n) → List (Circuit n)
  | [] => []
  | [c] => [c]
  | c₁ :: c₂ :: cs => Circuit.node b [c₁, c₂] :: pairUp b cs

/-- Pairing halves the list, rounding up. -/
private theorem length_pairUp (b : Bool) :
    ∀ cs : List (Circuit n), (pairUp b cs).length = (cs.length + 1) / 2
  | [] => by simp [pairUp]
  | [_] => by simp [pairUp]
  | _ :: _ :: cs => by
      have := length_pairUp b cs
      simp only [pairUp, List.length_cons] at *
      omega

/-- Pairing preserves the value of the surrounding gate. -/
private theorem eval_node_pairUp (b : Bool) (x : Fin n → Bool) :
    ∀ cs : List (Circuit n),
      (Circuit.node b (pairUp b cs)).eval x = (Circuit.node b cs).eval x
  | [] => rfl
  | [_] => by cases b <;> simp [pairUp, Circuit.eval]
  | c₁ :: c₂ :: cs => by
      have := eval_node_pairUp b x cs
      cases b <;>
        simp only [pairUp, Circuit.eval, List.foldr_cons, List.foldr_nil] at * <;>
        simp [this, Bool.and_assoc, Bool.or_assoc]

/-- Pairing adds at most one to the depth. -/
private theorem maxDepth_pairUp (b : Bool) :
    ∀ cs : List (Circuit n), Circuit.maxDepth (pairUp b cs) ≤ 1 + Circuit.maxDepth cs
  | [] => by simp [pairUp, Circuit.maxDepth_nil]
  | [c] => by simp [pairUp]
  | c₁ :: c₂ :: cs => by
      have ih := maxDepth_pairUp b cs
      have h1 : (Circuit.node b [c₁, c₂]).depth
          = 1 + max c₁.depth (max c₂.depth 0) := by
        rw [Circuit.depth_node, Circuit.maxDepth_cons, Circuit.maxDepth_cons, Circuit.maxDepth_nil]
      simp only [pairUp, Circuit.maxDepth_cons, h1]
      omega

/-- Pairing does not increase the total size plus length. -/
private theorem sumSize_pairUp (b : Bool) :
    ∀ cs : List (Circuit n),
      Circuit.sumSize (pairUp b cs) + (pairUp b cs).length ≤
        Circuit.sumSize cs + cs.length
  | [] => le_refl 0
  | [_] => le_refl _
  | c₁ :: c₂ :: cs => by
      have ih := sumSize_pairUp b cs
      have h1 : (Circuit.node b [c₁, c₂]).size = 1 + (c₁.size + (c₂.size + 0)) := by
        rw [Circuit.size_node, Circuit.sumSize_cons, Circuit.sumSize_cons, Circuit.sumSize_nil]
      simp only [pairUp, Circuit.sumSize_cons, h1, List.length_cons]
      omega

/-- Pairing introduces only fan-in-2 gates. -/
private theorem maxFaninL_pairUp (b : Bool) :
    ∀ cs : List (Circuit n), Circuit.maxFaninL (pairUp b cs) ≤ max 2 (Circuit.maxFaninL cs)
  | [] => Nat.zero_le _
  | [c] => by simp [pairUp, Circuit.maxFaninL_cons, Circuit.maxFaninL_nil]
  | c₁ :: c₂ :: cs => by
      have ih := maxFaninL_pairUp b cs
      have h1 : (Circuit.node b [c₁, c₂]).maxFanin
          = max 2 (max c₁.maxFanin (max c₂.maxFanin 0)) := by
        rw [Circuit.maxFanin_node, Circuit.maxFaninL_cons, Circuit.maxFaninL_cons,
          Circuit.maxFaninL_nil]
        norm_num
      simp only [pairUp, Circuit.maxFaninL_cons, h1]
      omega

/-- Repeatedly pair a child list, `k` rounds at most, into a single circuit. -/
private def combineFuel (b : Bool) : ℕ → List (Circuit n) → Circuit n
  | 0, cs => Circuit.node b cs
  | _ + 1, [] => Circuit.node b []
  | _ + 1, [c] => c
  | k + 1, c₁ :: c₂ :: cs => combineFuel b k (pairUp b (c₁ :: c₂ :: cs))

/-- Combine a child list into a balanced binary tree of gates of type `b`. -/
private def combine (b : Bool) (cs : List (Circuit n)) : Circuit n :=
  combineFuel b cs.length cs

/-- Combining computes the same value as the unbounded gate. -/
private theorem combineFuel_eval (b : Bool) (x : Fin n → Bool) :
    ∀ (k : ℕ) (cs : List (Circuit n)),
      (combineFuel b k cs).eval x = (Circuit.node b cs).eval x
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | _ + 1, [c] => by cases b <;> simp [combineFuel, Circuit.eval]
  | k + 1, c₁ :: c₂ :: cs => by
      show (combineFuel b k (pairUp b (c₁ :: c₂ :: cs))).eval x = _
      rw [combineFuel_eval b x k, eval_node_pairUp]

/-- Combining produces only fan-in-2 gates, given enough rounds. -/
private theorem combineFuel_maxFanin (b : Bool) :
    ∀ (k : ℕ) (cs : List (Circuit n)), cs.length ≤ k →
      (combineFuel b k cs).maxFanin ≤ max 2 (Circuit.maxFaninL cs)
  | 0, [], _ => by simp [combineFuel, Circuit.maxFanin_node, Circuit.maxFaninL_nil]
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], _ => by simp [combineFuel, Circuit.maxFanin_node, Circuit.maxFaninL_nil]
  | _ + 1, [c], _ => by
      show c.maxFanin ≤ _
      rw [Circuit.maxFaninL_cons, Circuit.maxFaninL_nil]
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
    ∀ (k : ℕ) (cs : List (Circuit n)), cs.length ≤ k →
      (combineFuel b k cs).depth ≤ Circuit.maxDepth cs + Nat.clog 2 cs.length + 1
  | 0, [], _ => by simp [combineFuel, Circuit.depth_node, Circuit.maxDepth_nil]
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], _ => by simp [combineFuel, Circuit.depth_node, Circuit.maxDepth_nil]
  | _ + 1, [c], _ => by
      show c.depth ≤ _
      rw [Circuit.maxDepth_cons, Circuit.maxDepth_nil]
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
    ∀ (k : ℕ) (cs : List (Circuit n)),
      (combineFuel b k cs).size ≤ Circuit.sumSize cs + cs.length + 1
  | 0, cs => by show (Circuit.node b cs).size ≤ _; rw [Circuit.size_node]; omega
  | _ + 1, [] => by simp [combineFuel, Circuit.size_node, Circuit.sumSize_nil]
  | _ + 1, [c] => by show c.size ≤ _; rw [Circuit.sumSize_cons, Circuit.sumSize_nil]; omega
  | k + 1, c₁ :: c₂ :: cs => by
      have ih := combineFuel_size b k (pairUp b (c₁ :: c₂ :: cs))
      have h2 := sumSize_pairUp b (c₁ :: c₂ :: cs)
      show (combineFuel b k (pairUp b (c₁ :: c₂ :: cs))).size ≤ _
      omega

/-- `combine` computes the unbounded gate. -/
private theorem combine_eval (b : Bool) (cs : List (Circuit n)) (x : Fin n → Bool) :
    (combine b cs).eval x = (Circuit.node b cs).eval x :=
  combineFuel_eval b x _ cs

/-- `combine` has fan-in 2, unless a child already had more. -/
private theorem combine_maxFanin (b : Bool) (cs : List (Circuit n)) :
    (combine b cs).maxFanin ≤ max 2 (Circuit.maxFaninL cs) :=
  combineFuel_maxFanin b _ cs (le_refl _)

/-- `combine` adds `⌈log₂ |cs|⌉ + 1` to the children's depth. -/
private theorem combine_depth (b : Bool) (cs : List (Circuit n)) :
    (combine b cs).depth ≤ Circuit.maxDepth cs + Nat.clog 2 cs.length + 1 :=
  combineFuel_depth b _ cs (le_refl _)

/-- `combine` adds `|cs| + 1` to the children's total size. -/
private theorem combine_size (b : Bool) (cs : List (Circuit n)) :
    (combine b cs).size ≤ Circuit.sumSize cs + cs.length + 1 :=
  combineFuel_size b _ cs

/-- Rebuild every gate of a circuit as a balanced binary tree of gates of the same
type, so that the result has fan-in `2`.  [AB09, p. 118] -/
def Circuit.toBinary : Circuit n → Circuit n
  | .lit l => .lit l
  | .node b cs => combine b (cs.map Circuit.toBinary)

/-- A gate's value is unchanged when its children are replaced by equivalent ones. -/
private theorem eval_node_map (b : Bool) (x : Fin n → Bool) (f : Circuit n → Circuit n) :
    ∀ cs : List (Circuit n), (∀ c ∈ cs, (f c).eval x = c.eval x) →
      (Circuit.node b (cs.map f)).eval x = (Circuit.node b cs).eval x
  | [], _ => rfl
  | c :: cs, h => by
      have ih := eval_node_map b x f cs (fun d hd => h d (List.mem_cons_of_mem _ hd))
      have hc := h c (List.mem_cons_self ..)
      cases b <;>
        simp only [List.map_cons, Circuit.eval, List.foldr_cons] at ih ⊢ <;>
        rw [hc, ih]

/-- A depth bound on every image element bounds the image's depth. -/
private theorem maxDepth_map_le (f : Circuit n → Circuit n) (m : ℕ) :
    ∀ cs : List (Circuit n), (∀ c ∈ cs, (f c).depth ≤ m) →
      Circuit.maxDepth (cs.map f) ≤ m
  | [], _ => Nat.zero_le _
  | c :: cs, h => by
      have ih := maxDepth_map_le f m cs (fun d hd => h d (List.mem_cons_of_mem _ hd))
      have hc := h c (List.mem_cons_self ..)
      simp only [List.map_cons, Circuit.maxDepth_cons]
      omega

/-- A fan-in bound on every image element bounds the image's fan-in. -/
private theorem maxFaninL_map_le (f : Circuit n → Circuit n) (m : ℕ) :
    ∀ cs : List (Circuit n), (∀ c ∈ cs, (f c).maxFanin ≤ m) →
      Circuit.maxFaninL (cs.map f) ≤ m
  | [], _ => Nat.zero_le _
  | c :: cs, h => by
      have ih := maxFaninL_map_le f m cs (fun d hd => h d (List.mem_cons_of_mem _ hd))
      have hc := h c (List.mem_cons_self ..)
      simp only [List.map_cons, Circuit.maxFaninL_cons]
      omega

/-- `toBinary` computes the same function. -/
theorem toBinary_eval : ∀ (c : Circuit n) (x : Fin n → Bool), c.toBinary.eval x = c.eval x := by
  intro c
  induction c using Circuit.ind with
  | hlit l => intro x; simp only [Circuit.toBinary]
  | hnode b cs ih =>
      intro x
      simp only [Circuit.toBinary]
      rw [combine_eval]
      exact eval_node_map b x Circuit.toBinary cs (fun c hc => ih c hc x)

/-- `toBinary` produces a fan-in-2 circuit. -/
theorem toBinary_maxFanin_le : ∀ c : Circuit n, c.toBinary.maxFanin ≤ 2 := by
  intro c
  induction c using Circuit.ind with
  | hlit l => simp [Circuit.toBinary, Circuit.maxFanin]
  | hnode b cs ih =>
      simp only [Circuit.toBinary]
      have h1 := combine_maxFanin b (cs.map Circuit.toBinary)
      have h2 := maxFaninL_map_le Circuit.toBinary 2 cs ih
      omega

/-- The list form of `toBinary_size_le`, in the strengthened form the induction needs. -/
private theorem sumSize_map_toBinary :
    ∀ cs : List (Circuit n), (∀ c ∈ cs, c.toBinary.size + 1 ≤ 3 * c.size) →
      Circuit.sumSize (cs.map Circuit.toBinary) + cs.length ≤ 3 * Circuit.sumSize cs
  | [], _ => by simp [Circuit.sumSize_nil]
  | c :: cs, h => by
      have ih := sumSize_map_toBinary cs (fun d hd => h d (List.mem_cons_of_mem _ hd))
      have hc := h c (List.mem_cons_self ..)
      simp only [List.map_cons, Circuit.sumSize_cons, List.length_cons]
      omega

/-- `toBinary` at most triples the size, with one unit to spare. -/
private theorem toBinary_size_succ_le : ∀ c : Circuit n, c.toBinary.size + 1 ≤ 3 * c.size := by
  intro c
  induction c using Circuit.ind with
  | hlit l => simp [Circuit.toBinary, Circuit.size]
  | hnode b cs ih =>
      simp only [Circuit.toBinary]
      have h1 := combine_size b (cs.map Circuit.toBinary)
      have h2 := sumSize_map_toBinary cs ih
      rw [Circuit.size_node]
      simp only [List.length_map] at h1
      omega

/-- `toBinary` at most triples the size. -/
theorem toBinary_size_le (c : Circuit n) : c.toBinary.size ≤ 3 * c.size :=
  le_trans (Nat.le_succ _) (toBinary_size_succ_le c)

/-- `toBinary` multiplies the depth by `⌈log₂ w⌉ + 1`, where `w` bounds the fan-in. -/
theorem toBinary_depth_le {w : ℕ} : ∀ c : Circuit n, c.maxFanin ≤ w →
    c.toBinary.depth ≤ c.depth * (Nat.clog 2 w + 1) := by
  intro c
  induction c using Circuit.ind with
  | hlit l => intro _; simp [Circuit.toBinary, Circuit.depth]
  | hnode b cs ih =>
      intro h
      rw [Circuit.maxFanin_node] at h
      have hlen : cs.length ≤ w := le_trans (le_max_left _ _) h
      have hfan : Circuit.maxFaninL cs ≤ w := le_trans (le_max_right _ _) h
      have hB : Circuit.maxDepth (cs.map Circuit.toBinary)
          ≤ Circuit.maxDepth cs * (Nat.clog 2 w + 1) :=
        maxDepth_map_le _ _ cs fun c hc =>
          le_trans (ih c hc (le_trans (Circuit.maxFanin_le_maxFaninL hc) hfan))
            (Nat.mul_le_mul_right _ (Circuit.depth_le_maxDepth hc))
      have hC : Nat.clog 2 cs.length ≤ Nat.clog 2 w := Nat.clog_mono_right 2 hlen
      simp only [Circuit.toBinary]
      refine le_trans (combine_depth b (cs.map Circuit.toBinary)) ?_
      rw [Circuit.depth_node, Nat.add_mul, Nat.one_mul, List.length_map]
      omega

/-- `⌈log₂⌉` of a polynomial is `O(log n)`. -/
private theorem clog_poly_le (a k m : ℕ) :
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
`Circuit.toBinary`'s balanced binary tree of gates of the same type multiplies the depth by
`⌈log₂ w⌉ + 1`, so the new depth is at most `b(a+k+1)(log n+1)^{i+1}`; it at most triples
the size, so the family is still polynomial; it has fan-in `2`; and it computes the same
function, so it decides the same language. -/
theorem Language.InAC.inNC_succ {d : ℕ} {L : Language Bool} (h : L.InAC d) :
    L.InNC (d + 1) := by
  classical
  obtain ⟨C, ⟨a, k, hsize⟩, ⟨b, hdepth⟩, hlang⟩ := h
  refine ⟨⟨fun n => (C.circuit n).toBinary⟩, fun n => BoolCircuit.toBinary_maxFanin_le _,
    ⟨3 * a, k, fun n => ?_⟩, ⟨b * (a + k + 1), fun n => ?_⟩, ?_⟩
  · calc ((C.circuit n).toBinary).size
        ≤ 3 * (C.circuit n).size := BoolCircuit.toBinary_size_le _
      _ ≤ 3 * (a * (n + 1) ^ k) := Nat.mul_le_mul_left 3 (hsize n)
      _ = 3 * a * (n + 1) ^ k := (Nat.mul_assoc 3 a _).symm
  · have hfan : (C.circuit n).maxFanin ≤ a * (n + 1) ^ k :=
      le_trans (BoolCircuit.Circuit.maxFanin_le_size _) (hsize n)
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
theorem NCLevel_subset_ACLevel (i : ℕ) : NCLevel i ⊆ ACLevel i :=
  fun _ h => Language.InNC.inAC h

/-- `AC^i ⊆ NC^{i+1}`.  [AB09, p. 118] -/
theorem ACLevel_subset_NCLevel_succ (i : ℕ) : ACLevel i ⊆ NCLevel (i + 1) :=
  fun _ h => Language.InAC.inNC_succ h

/-- The two inclusions collapse the hierarchies: `NC = AC`, a corollary of
[AB09, p. 118], which states the inclusions only. -/
theorem NC_eq_AC : NC = AC := by
  ext L
  rw [mem_NC_iff, mem_AC_iff]
  constructor
  · rintro ⟨i, _, hi⟩
    exact ⟨i, hi.inAC⟩
  · rintro ⟨i, hi⟩
    exact ⟨i + 1, Nat.le_add_left 1 i, hi.inNC_succ⟩

end BoolCircuit
