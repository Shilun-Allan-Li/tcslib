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
* `Language.parity` — [AB09, Ex 6.26]'s `PARITY`, and `BoolCircuit.parityCircuit`.

## Main results

* `Language.InNC.inAC` and `Language.InAC.inNC_succ` — `NC^i ⊆ AC^i ⊆ NC^{i+1}`
  [AB09, p. 118], hence `BoolCircuit.NC_eq_AC`.
* `BoolCircuit.toBinary_eval`, `toBinary_maxFanin_le`, `toBinary_depth_le`,
  `toBinary_size_le` — the four facts that inclusion needs.
* `Language.parity_inNC_one` — [AB09, Ex 6.26], `PARITY ∈ NC¹`.

## Divergences from Arora–Barak §6.7.1

* **Circuit model.** `BoolCircuit.Circuit` is a *tree*: every gate feeds exactly one
  parent, so this is AB's class with fan-out 1 (a formula, in the usual terminology).
  The three results below are theorems about that model.  `NC¹` is unaffected — a
  fan-in-2 tree of depth `O(log n)` has `poly(n)` nodes, and conversely — but for
  `i ≥ 2` a fan-out-1 `NC^i` is contained in, and not known to equal, AB's.  The
  alternative, `ACP.FeedForward`, is a layered DAG and is what `PPoly.lean` uses; it
  was rejected here because `toBinary` — which must *build* a `⌈log₂ w⌉`-deep tree in
  place of a width-`w` gate — is a recursion over a gate's child list, and
  `FeedForward` has no child list to recurse on.  Consequently `NC ⊆ P/poly` is not
  statable: the two classes are over different circuit types.
* **Fan-in.** Bounded fan-in is the predicate `Circuit.maxFanin ≤ 2` over the one
  unbounded-fan-in `Circuit` type, not a separate inductive type — this is the idiom
  the LMN development already uses (`maxFanin ≤ w` as a hypothesis), and it lets
  `toBinary : Circuit n → Circuit n` be a plain function whose four properties are
  ordinary lemmas about one type.
* **Negation.** `Circuit` negates only at literals, so a `NOT` gate is free and
  contributes no depth.  Every circuit built here is in that De Morgan normal form
  anyway, which is why `PARITY` is built as a dual pair (a circuit and a circuit for
  its complement) rather than with internal negations.
* **`O(log^d n)`.** Written `∃ b, ∀ n, depth ≤ b * (Nat.log 2 n + 1) ^ d`, the shape
  `PPoly.lean` uses for size.  The `+ 1` repairs the same degeneracy: `Nat.log 2 n = 0`
  for `n ≤ 1`, so `b * (Nat.log 2 n) ^ d` would force depth `0` at those lengths.
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

/-! ### Structural unfoldings -/

/-- Maximum fan-in over a list of circuits. -/
private def maxFaninL (cs : List (Circuit n)) : ℕ :=
  cs.foldr (fun c acc => max c.maxFanin acc) 0

/-- A gate's depth is one more than its children's. -/
private theorem depth_node (b : Bool) (cs : List (Circuit n)) :
    (Circuit.node b cs).depth = 1 + Circuit.maxDepth cs := by
  simp [Circuit.depth, Circuit.maxDepth]

/-- A gate's size is one more than its children's total. -/
private theorem size_node (b : Bool) (cs : List (Circuit n)) :
    (Circuit.node b cs).size = 1 + Circuit.sumSize cs := by
  simp [Circuit.size, Circuit.sumSize]

/-- A gate's fan-in is its arity or its children's fan-in, whichever is larger. -/
private theorem maxFanin_node (b : Bool) (cs : List (Circuit n)) :
    (Circuit.node b cs).maxFanin = max cs.length (maxFaninL cs) := by
  simp [Circuit.maxFanin, maxFaninL]

/-- `maxDepth` of the empty list. -/
private theorem maxDepth_nil : Circuit.maxDepth ([] : List (Circuit n)) = 0 := rfl

/-- `maxDepth` on a cons cell. -/
private theorem maxDepth_cons (c : Circuit n) (cs : List (Circuit n)) :
    Circuit.maxDepth (c :: cs) = max c.depth (Circuit.maxDepth cs) := rfl

/-- `sumSize` of the empty list. -/
private theorem sumSize_nil : Circuit.sumSize ([] : List (Circuit n)) = 0 := rfl

/-- `sumSize` on a cons cell. -/
private theorem sumSize_cons (c : Circuit n) (cs : List (Circuit n)) :
    Circuit.sumSize (c :: cs) = c.size + Circuit.sumSize cs := rfl

/-- `maxFaninL` of the empty list. -/
private theorem maxFaninL_nil : maxFaninL ([] : List (Circuit n)) = 0 := rfl

/-- `maxFaninL` on a cons cell. -/
private theorem maxFaninL_cons (c : Circuit n) (cs : List (Circuit n)) :
    maxFaninL (c :: cs) = max c.maxFanin (maxFaninL cs) := rfl

/-- Each child is no deeper than the deepest. -/
private theorem depth_le_maxDepth {c : Circuit n} :
    ∀ {cs : List (Circuit n)}, c ∈ cs → c.depth ≤ Circuit.maxDepth cs
  | _ :: cs, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact le_max_left _ _
      · exact (depth_le_maxDepth h).trans (le_max_right _ _)

/-- Each child's fan-in is at most the list's. -/
private theorem maxFanin_le_maxFaninL {c : Circuit n} :
    ∀ {cs : List (Circuit n)}, c ∈ cs → c.maxFanin ≤ maxFaninL cs
  | _ :: cs, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact le_max_left _ _
      · exact (maxFanin_le_maxFaninL h).trans (le_max_right _ _)

/-- A circuit has at least one node, so a child list is no longer than its total size. -/
private theorem length_le_sumSize : ∀ cs : List (Circuit n), cs.length ≤ Circuit.sumSize cs
  | [] => le_refl 0
  | c :: cs => by
      have hc : 1 ≤ c.size := by cases c <;> simp [Circuit.size]
      have := length_le_sumSize cs
      simp only [List.length_cons, sumSize_cons]
      omega

/-- The list form of `Circuit.maxFanin_le_size`. -/
private theorem maxFaninL_le_sumSize :
    ∀ {cs : List (Circuit n)}, (∀ c ∈ cs, c.maxFanin ≤ c.size) →
      maxFaninL cs ≤ Circuit.sumSize cs
  | [], _ => le_refl 0
  | c :: cs, h => by
      have h1 := h c (List.mem_cons_self ..)
      have h2 := maxFaninL_le_sumSize (fun d hd => h d (List.mem_cons_of_mem _ hd))
      simp only [maxFaninL_cons, sumSize_cons]
      omega

/-- A circuit's fan-in is bounded by its size. -/
theorem Circuit.maxFanin_le_size (c : Circuit n) : c.maxFanin ≤ c.size := by
  induction c using Circuit.ind with
  | hlit l => simp [Circuit.maxFanin, Circuit.size]
  | hnode b cs ih =>
      have h₁ := length_le_sumSize cs
      have h₂ := maxFaninL_le_sumSize ih
      rw [maxFanin_node, size_node]
      omega

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
  | [] => by simp [pairUp, maxDepth_nil]
  | [c] => by simp [pairUp]
  | c₁ :: c₂ :: cs => by
      have ih := maxDepth_pairUp b cs
      have h1 : (Circuit.node b [c₁, c₂]).depth
          = 1 + max c₁.depth (max c₂.depth 0) := by
        rw [depth_node, maxDepth_cons, maxDepth_cons, maxDepth_nil]
      simp only [pairUp, maxDepth_cons, h1]
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
        rw [size_node, sumSize_cons, sumSize_cons, sumSize_nil]
      simp only [pairUp, sumSize_cons, h1, List.length_cons]
      omega

/-- Pairing introduces only fan-in-2 gates. -/
private theorem maxFaninL_pairUp (b : Bool) :
    ∀ cs : List (Circuit n), maxFaninL (pairUp b cs) ≤ max 2 (maxFaninL cs)
  | [] => Nat.zero_le _
  | [c] => by simp [pairUp, maxFaninL_cons, maxFaninL_nil]
  | c₁ :: c₂ :: cs => by
      have ih := maxFaninL_pairUp b cs
      have h1 : (Circuit.node b [c₁, c₂]).maxFanin
          = max 2 (max c₁.maxFanin (max c₂.maxFanin 0)) := by
        rw [maxFanin_node, maxFaninL_cons, maxFaninL_cons, maxFaninL_nil]
        norm_num
      simp only [pairUp, maxFaninL_cons, h1]
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
      (combineFuel b k cs).maxFanin ≤ max 2 (maxFaninL cs)
  | 0, [], _ => by simp [combineFuel, maxFanin_node, maxFaninL_nil]
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], _ => by simp [combineFuel, maxFanin_node, maxFaninL_nil]
  | _ + 1, [c], _ => by
      show c.maxFanin ≤ _
      rw [maxFaninL_cons, maxFaninL_nil]
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
  | 0, [], _ => by simp [combineFuel, depth_node, maxDepth_nil]
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], _ => by simp [combineFuel, depth_node, maxDepth_nil]
  | _ + 1, [c], _ => by
      show c.depth ≤ _
      rw [maxDepth_cons, maxDepth_nil]
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
  | 0, cs => by show (Circuit.node b cs).size ≤ _; rw [size_node]; omega
  | _ + 1, [] => by simp [combineFuel, size_node, sumSize_nil]
  | _ + 1, [c] => by show c.size ≤ _; rw [sumSize_cons, sumSize_nil]; omega
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
    (combine b cs).maxFanin ≤ max 2 (maxFaninL cs) :=
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
      simp only [List.map_cons, maxDepth_cons]
      omega

/-- A fan-in bound on every image element bounds the image's fan-in. -/
private theorem maxFaninL_map_le (f : Circuit n → Circuit n) (m : ℕ) :
    ∀ cs : List (Circuit n), (∀ c ∈ cs, (f c).maxFanin ≤ m) → maxFaninL (cs.map f) ≤ m
  | [], _ => Nat.zero_le _
  | c :: cs, h => by
      have ih := maxFaninL_map_le f m cs (fun d hd => h d (List.mem_cons_of_mem _ hd))
      have hc := h c (List.mem_cons_self ..)
      simp only [List.map_cons, maxFaninL_cons]
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
  | [], _ => by simp [sumSize_nil]
  | c :: cs, h => by
      have ih := sumSize_map_toBinary cs (fun d hd => h d (List.mem_cons_of_mem _ hd))
      have hc := h c (List.mem_cons_self ..)
      simp only [List.map_cons, sumSize_cons, List.length_cons]
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
      rw [size_node]
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
      rw [maxFanin_node] at h
      have hlen : cs.length ≤ w := le_trans (le_max_left _ _) h
      have hfan : maxFaninL cs ≤ w := le_trans (le_max_right _ _) h
      have hB : Circuit.maxDepth (cs.map Circuit.toBinary)
          ≤ Circuit.maxDepth cs * (Nat.clog 2 w + 1) :=
        maxDepth_map_le _ _ cs fun c hc =>
          le_trans (ih c hc (le_trans (maxFanin_le_maxFaninL hc) hfan))
            (Nat.mul_le_mul_right _ (depth_le_maxDepth hc))
      have hC : Nat.clog 2 cs.length ≤ Nat.clog 2 w := Nat.clog_mono_right 2 hlen
      simp only [Circuit.toBinary]
      refine le_trans (combine_depth b (cs.map Circuit.toBinary)) ?_
      rw [depth_node, Nat.add_mul, Nat.one_mul, List.length_map]
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

/-- The two inclusions collapse the hierarchies: `NC = AC`.  [AB09, p. 118] -/
theorem NC_eq_AC : NC = AC := by
  ext L
  rw [mem_NC_iff, mem_AC_iff]
  constructor
  · rintro ⟨i, _, hi⟩
    exact ⟨i, hi.inAC⟩
  · rintro ⟨i, hi⟩
    exact ⟨i + 1, Nat.le_add_left 1 i, hi.inNC_succ⟩

end BoolCircuit

namespace BoolCircuit

variable {n : ℕ}

/-! ### Size from depth, and `PARITY` -/

/-- A uniform bound on the children bounds the total size plus length. -/
private theorem sumSize_add_length_le (m : ℕ) :
    ∀ cs : List (Circuit n), (∀ c ∈ cs, c.size + 1 ≤ m) →
      Circuit.sumSize cs + cs.length ≤ cs.length * m
  | [], _ => by simp [sumSize_nil]
  | c :: cs, h => by
      have ih := sumSize_add_length_le m cs (fun d hd => h d (List.mem_cons_of_mem _ hd))
      have hc := h c (List.mem_cons_self ..)
      simp only [sumSize_cons, List.length_cons, Nat.succ_mul]
      omega

/-- A fan-in-2 circuit of depth `d` has at most `2 ^ (d + 1) - 1` nodes. -/
theorem Circuit.size_succ_le_two_pow : ∀ c : Circuit n, c.maxFanin ≤ 2 →
    c.size + 1 ≤ 2 ^ (c.depth + 1) := by
  intro c
  induction c using Circuit.ind with
  | hlit l => intro _; simp [Circuit.size, Circuit.depth]
  | hnode b cs ih =>
      intro h
      rw [maxFanin_node] at h
      have hlen : cs.length ≤ 2 := le_trans (le_max_left _ _) h
      have hfan : maxFaninL cs ≤ 2 := le_trans (le_max_right _ _) h
      have hchild : ∀ c ∈ cs, c.size + 1 ≤ 2 ^ (Circuit.maxDepth cs + 1) := fun c hc =>
        le_trans (ih c hc (le_trans (maxFanin_le_maxFaninL hc) hfan))
          (Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_succ (depth_le_maxDepth hc)))
      have hsum := sumSize_add_length_le _ cs hchild
      have hpos : 1 ≤ 2 ^ (Circuit.maxDepth cs + 1) := Nat.one_le_two_pow
      have hD : (2 : ℕ) ^ (Circuit.maxDepth cs + 2) = 2 * 2 ^ (Circuit.maxDepth cs + 1) := by
        ring
      rw [size_node, depth_node, show (1 : ℕ) + Circuit.maxDepth cs + 1
        = Circuit.maxDepth cs + 2 from by omega]
      rcases Nat.lt_or_ge cs.length 1 with hz | hz
      · have hnil : cs = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hnil
        simp only [sumSize_nil]
        omega
      · rcases Nat.lt_or_ge cs.length 2 with hz2 | hz2
        · rw [show cs.length = 1 from by omega, Nat.one_mul] at hsum
          omega
        · rw [show cs.length = 2 from by omega] at hsum
          omega

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
  simp only [xorNode, depth_node, maxDepth_cons, maxDepth_nil]
  omega

/-- `xorNode` introduces only fan-in-2 gates. -/
private theorem pairFanin_xorNode (p q : Circuit n × Circuit n) :
    max (xorNode p q).1.maxFanin (xorNode p q).2.maxFanin
      ≤ max 2 (max (max p.1.maxFanin p.2.maxFanin) (max q.1.maxFanin q.2.maxFanin)) := by
  simp only [xorNode, maxFanin_node, maxFaninL_cons, maxFaninL_nil, List.length_cons,
    List.length_nil]
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

/-- Repeatedly pair and XOR, `k` rounds at most. -/
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
  | 0, [], _ => by simp [xorFuel, depth_node, maxDepth_nil, pairDepth]
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], _ => by simp [xorFuel, depth_node, maxDepth_nil, pairDepth]
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
  | 0, [], _ => by simp [xorFuel, maxFanin_node, maxFaninL_nil]
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], _ => by simp [xorFuel, maxFanin_node, maxFaninL_nil]
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

end BoolCircuit
