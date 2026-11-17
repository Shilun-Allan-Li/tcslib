/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Computability.Language
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Log
import TCSlib.Complexity.CircuitComplexity.Basic
import TCSlib.Complexity.CircuitComplexity.FormulaArith.Combinators

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

/-- Reader of `IsPolySize`: `C.IsPolySize ↔ ∃ a k, ∀ n, (C.circuit n).size ≤ a * (n + 1) ^ k`.
Glue. -/
theorem isPolySize_iff :
    C.IsPolySize ↔ ∃ a k : ℕ, ∀ n, (C.circuit n).size ≤ a * (n + 1) ^ k :=
  Iff.rfl

/-- Every gate of every circuit in the family has at most two inputs. -/
def HasFaninTwo : Prop :=
  ∀ n, (C.circuit n).maxFanin ≤ 2

/-- Reader of `HasFaninTwo`: `C.HasFaninTwo ↔ ∀ n, (C.circuit n).maxFanin ≤ 2`.  Glue. -/
theorem hasFaninTwo_iff : C.HasFaninTwo ↔ ∀ n, (C.circuit n).maxFanin ≤ 2 :=
  Iff.rfl

/-- The family has polylogarithmic depth `O(log^d n)` (constant depth when `d = 0`). -/
def HasPolylogDepth (d : ℕ) : Prop :=
  ∃ b : ℕ, ∀ n, (C.circuit n).depth ≤ b * (Nat.log 2 n + 1) ^ d

/-- Reader of `HasPolylogDepth`:
`C.HasPolylogDepth d ↔ ∃ b, ∀ n, (C.circuit n).depth ≤ b * (Nat.log 2 n + 1) ^ d`.  Glue. -/
theorem hasPolylogDepth_iff (d : ℕ) :
    C.HasPolylogDepth d ↔ ∃ b : ℕ, ∀ n, (C.circuit n).depth ≤ b * (Nat.log 2 n + 1) ^ d :=
  Iff.rfl

end TreeCircuitFamily

end BoolCircuit

/-- `L ∈ NC^d`: a polynomial-size fan-in-2 family of depth `O(log^d n)` decides `L`.
[AB09, Def 6.24] -/
def Language.InTreeNC (d : ℕ) (L : Language Bool) : Prop :=
  ∃ C : BoolCircuit.TreeCircuitFamily,
    C.HasFaninTwo ∧ C.IsPolySize ∧ C.HasPolylogDepth d ∧ C.language = L

/-- Reader of `Language.InTreeNC`: `L.InTreeNC d ↔ ∃ C : TreeCircuitFamily, C.HasFaninTwo ∧
C.IsPolySize ∧ C.HasPolylogDepth d ∧ C.language = L`.  Glue. -/
theorem Language.inTreeNC_iff (d : ℕ) (L : Language Bool) :
    L.InTreeNC d ↔ ∃ C : BoolCircuit.TreeCircuitFamily,
      C.HasFaninTwo ∧ C.IsPolySize ∧ C.HasPolylogDepth d ∧ C.language = L :=
  Iff.rfl

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

/-- Rebuild every gate of a circuit as a balanced binary tree of gates of the same
type, so that the result has fan-in `2`.  [AB09, p. 118] -/
def TreeCircuit.toBinary : TreeCircuit n → TreeCircuit n
  | .lit l => .lit l
  | .node b cs => TreeCircuit.balanced b (cs.map TreeCircuit.toBinary)

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

/-- `toBinary` computes the same function. -/
theorem toBinary_eval : ∀ (c : TreeCircuit n) (x : Fin n → Bool), c.toBinary.eval x = c.eval x := by
  intro c
  induction c using TreeCircuit.ind with
  | hlit l => intro x; simp only [TreeCircuit.toBinary]
  | hnode b cs ih =>
      intro x
      simp only [TreeCircuit.toBinary]
      rw [TreeCircuit.balanced_eval]
      exact eval_node_map b x TreeCircuit.toBinary cs (fun c hc => ih c hc x)

/-- `toBinary` produces a fan-in-2 circuit. -/
theorem toBinary_maxFanin_le : ∀ c : TreeCircuit n, c.toBinary.maxFanin ≤ 2 := by
  intro c
  induction c using TreeCircuit.ind with
  | hlit l => simp [TreeCircuit.toBinary, TreeCircuit.maxFanin]
  | hnode b cs ih =>
      simp only [TreeCircuit.toBinary]
      have h1 := TreeCircuit.maxFanin_balanced_le b (cs.map TreeCircuit.toBinary)
      have h2 : TreeCircuit.maxFaninL (cs.map TreeCircuit.toBinary) ≤ 2 :=
        TreeCircuit.maxFaninL_le_of_forall (List.forall_mem_map.mpr ih)
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
      have h1 := TreeCircuit.size_balanced_le b (cs.map TreeCircuit.toBinary)
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
        TreeCircuit.maxDepth_le_of_forall <| List.forall_mem_map.mpr fun c hc =>
          le_trans (ih c hc (le_trans (TreeCircuit.maxFanin_le_maxFaninL hc) hfan))
            (Nat.mul_le_mul_right _ (TreeCircuit.depth_le_maxDepth hc))
      have hC : Nat.clog 2 cs.length ≤ Nat.clog 2 w := Nat.clog_mono_right 2 hlen
      simp only [TreeCircuit.toBinary]
      refine le_trans (TreeCircuit.depth_balanced_le b (cs.map TreeCircuit.toBinary)) ?_
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
