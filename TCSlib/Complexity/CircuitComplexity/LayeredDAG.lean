/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.DAGFanin
import TCSlib.Complexity.CircuitComplexity.LayeredPPoly
import TCSlib.Complexity.CircuitComplexity.PPoly
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finite.Card

/-!
# Converting between layered circuits and DAG circuits

`BoolCircuit.LayeredCircuit` (layered DAGs over an arbitrary gate set; the carrier of
`Language.InLayeredPPoly` and of the Razborov–Smolensky development) and
`BoolCircuit.DAGCircuit` ([AB09, Def 6.1]) are related in both directions, at polynomial
cost, so the two definitions of `P/poly` coincide.

* **DAG → Layered** (`BoolCircuit.DAGCircuit.toLayered`): a well-formed DAG without `∨`
  gates (see `DAGCircuit.deMorgan`) becomes a layered circuit over `stdGateOps` with one
  DAG vertex per layer: layer `d` holds the inputs and the first `d` gates, earlier vertices
  are carried up by identity gates, and a last layer holds the output.  Size is at most
  `(#gates + 1) * (size + 1)`.
* **Layered → DAG** (`BoolCircuit.LayeredCircuit.toDAG`): a finite layered circuit over
  `stdGateOps` becomes a well-formed DAG with one gate per non-input node, so its size is
  exactly `n` plus the layered size.

## Main definitions

* `BoolCircuit.DAGCircuit.toLayered`, `BoolCircuit.LayeredCircuit.toDAG`.

## Main results

* `BoolCircuit.DAGCircuit.toLayered_eval₁`, `toLayered_size_le`, `toLayered_finite`,
  `toLayered_onlyUsesGates`.
* `BoolCircuit.LayeredCircuit.toDAG_eval`, `toDAG_size`, `toDAG_isWellFormed`.
* `Language.inPPoly_iff_inLayeredPPoly` — the two `P/poly`s coincide.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1.)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

open LayeredCircuit

/-! ## Evaluation of layered circuits, layer by layer -/

namespace LayeredCircuit

variable {α : Type} {inp out : Type} (F : LayeredCircuit α inp out)

theorem evalNode_zero (h : 0 < F.depth + 1) (u : F.nodes ⟨0, h⟩) (xs : inp → α) :
    F.evalNode u xs = xs (F.nodes_zero ▸ u) := rfl

theorem evalNode_succ {m : ℕ} (h : m + 1 < F.depth + 1) (u : F.nodes ⟨m + 1, h⟩)
    (xs : inp → α) :
    F.evalNode u xs = LayeredCircuit.Gate.eval (F.gates ⟨m, by omega⟩ u)
      (fun v => F.evalNode (d := ⟨m, by omega⟩) v xs) := rfl

theorem eval₁_eq [Unique out] (xs : inp → α) :
    F.eval₁ xs = F.evalNode (d := Fin.last F.depth) (F.nodes_last.symm.rec default) xs := rfl

end LayeredCircuit

/-! ## Bits and `Fin 2` -/

/-- A bit as an element of `Fin 2`, the layered model's alphabet. -/
abbrev b2f : Bool → Fin 2 := finTwoEquiv.symm

theorem b2f_and (a b : Bool) : b2f (a && b) = b2f a * b2f b := by cases a <;> cases b <;> rfl

theorem b2f_not (a : Bool) : b2f (!a) = 1 - b2f a := by cases a <;> rfl

theorem b2f_eq_one_iff (a : Bool) : b2f a = 1 ↔ a = true := by cases a <;> decide

theorem b2f_injective : Function.Injective b2f := finTwoEquiv.symm.injective

theorem prod_b2f_getElem (l : List ℕ) (f : ℕ → Bool) :
    ∏ j : Fin l.length, b2f (f l[j]) = b2f (l.all f) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show ∏ j : Fin (l.length + 1), b2f (f (a :: l)[j]) = _
    rw [Fin.prod_univ_succ]
    simp only [Fin.getElem_fin, Fin.val_zero, List.getElem_cons_zero, Fin.val_succ,
      List.getElem_cons_succ] at ih ⊢
    rw [ih, List.all_cons, b2f_and]

/-! ## DAG → Layered -/

/-- The layered gate computing a well-formed `∧` or `¬` gate whose inputs are the nodes
`emb a`.  (`∨` is mapped like `∧` but never occurs: apply `DAGCircuit.deMorgan` first.) -/
def layerGateOf {D : Type} (g : DAGGate) (hg : g.WellFormed) (emb : (a : ℕ) → a ∈ g.args → D) :
    Gate (Fin 2) D :=
  match hk : g.kind with
  | .not =>
    have h0 : 0 < g.args.length := by have := hg.2 hk; omega
    ⟨⟨Fin 1, fun x => 1 - x 0⟩, fun _ => emb g.args[0] (List.getElem_mem h0)⟩
  | .and => ⟨⟨Fin g.args.length, fun x => ∏ i, x i⟩, fun j => emb g.args[j] (List.getElem_mem _)⟩
  | .or => ⟨⟨Fin g.args.length, fun x => ∏ i, x i⟩, fun j => emb g.args[j] (List.getElem_mem _)⟩

theorem layerGateOf_mem {D : Type} (g : DAGGate) (hg : g.WellFormed)
    (emb : (a : ℕ) → a ∈ g.args → D) : (layerGateOf g hg emb).op ∈ stdGateOps := by
  unfold layerGateOf
  split
  · exact Or.inl (Or.inr rfl)
  · exact Or.inr (Set.mem_iUnion.mpr ⟨_, rfl⟩)
  · exact Or.inr (Set.mem_iUnion.mpr ⟨_, rfl⟩)

theorem layerGateOf_eval {D : Type} (g : DAGGate) (hg : g.WellFormed) (hno : g.kind ≠ .or)
    (emb : (a : ℕ) → a ∈ g.args → D) (vals : D → Fin 2) (vs : List Bool)
    (h : ∀ a (ha : a ∈ g.args), vals (emb a ha) = b2f (vs.getD a false)) :
    LayeredCircuit.Gate.eval (layerGateOf g hg emb) vals = b2f (g.eval vs) := by
  unfold layerGateOf
  split
  · rename_i hk
    have h0 : 0 < g.args.length := by have := hg.2 hk; omega
    obtain ⟨a, ha⟩ : ∃ a, g.args = [a] := List.length_eq_one_iff.mp (hg.2 hk)
    simp only [LayeredCircuit.Gate.eval, Function.comp_def]
    rw [h _ _, List.getElem_of_eq ha h0]
    simp [DAGGate.eval, hk, ha, b2f_not]
  · rename_i hk
    simp only [LayeredCircuit.Gate.eval, Function.comp_def]
    rw [Fintype.prod_congr _ _ fun j => h _ _]
    exact (prod_b2f_getElem g.args (fun a => vs.getD a false)).trans (by simp [DAGGate.eval, hk])
  · rename_i hk
    exact absurd hk hno

namespace DAGCircuit

variable {n : ℕ} (C : DAGCircuit n)

/-- Layer `d` of `C.toLayered`: the inputs and the first `d` gates, until the output
layer. -/
def layerNodes (d : Fin (C.gates.length + 2)) : Type :=
  if d.val ≤ C.gates.length then Fin (n + d.val) else Unit

/-- A vertex as a node of layer `d`. -/
def toNode {d : Fin (C.gates.length + 2)} (h : d.val ≤ C.gates.length) (i : Fin (n + d.val)) :
    C.layerNodes d :=
  cast (by rw [layerNodes, if_pos h]) i

/-- A node of layer `d` as a vertex. -/
def ofNode {d : Fin (C.gates.length + 2)} (h : d.val ≤ C.gates.length) (u : C.layerNodes d) :
    Fin (n + d.val) :=
  cast (by rw [layerNodes, if_pos h]) u

@[simp] theorem ofNode_toNode {d : Fin (C.gates.length + 2)} (h : d.val ≤ C.gates.length)
    (i : Fin (n + d.val)) : C.ofNode h (C.toNode h i) = i := by
  simp [ofNode, toNode]

instance (d : Fin (C.gates.length + 2)) : Finite (C.layerNodes d) := by
  unfold layerNodes; split <;> infer_instance

theorem castSucc_le (d : Fin (C.gates.length + 1)) : d.castSucc.val ≤ C.gates.length := by
  simp only [Fin.coe_castSucc]; omega

theorem succ_le {d : Fin (C.gates.length + 1)} (hd : d.val < C.gates.length) :
    d.succ.val ≤ C.gates.length := by
  simp only [Fin.val_succ]; omega

/-- The gate of the layered circuit from layer `d` to node `u` of layer `d + 1`: the output
gate (an identity on `C.output`) on the last step, an identity carrying an old vertex up, or
the layered version of gate `d`. -/
def layerGate (hwf : C.IsWellFormed) (d : Fin (C.gates.length + 1))
    (u : C.layerNodes d.succ) : Gate (Fin 2) (C.layerNodes d.castSucc) :=
  if hd : d.val < C.gates.length then
    if hu : (C.ofNode (C.succ_le hd) u).val < n + d.val then
      ⟨GateOp.id (Fin 2), fun _ => C.toNode (C.castSucc_le d) ⟨(C.ofNode (C.succ_le hd) u).val, hu⟩⟩
    else
      layerGateOf C.gates[d.val] (hwf _ (List.getElem_mem hd))
        fun a ha => C.toNode (C.castSucc_le d) ⟨a, C.args_lt d.val hd a ha⟩
  else
    ⟨GateOp.id (Fin 2), fun _ => C.toNode (C.castSucc_le d) ⟨C.output, by
      have := C.output_lt; simp only [Fin.coe_castSucc]; omega⟩⟩

/-- A well-formed DAG circuit as a layered circuit, one gate per layer. -/
def toLayered (hwf : C.IsWellFormed) : LayeredCircuit (Fin 2) (Fin n) Unit where
  depth := C.gates.length + 1
  nodes := C.layerNodes
  gates := C.layerGate hwf
  nodes_zero := by simp [layerNodes]
  nodes_last := by simp [layerNodes]

section ToLayered

variable (hwf : C.IsWellFormed)

theorem toLayered_finite : (C.toLayered hwf).Finite := fun d => inferInstanceAs
  (Finite (C.layerNodes d))

theorem toLayered_onlyUsesGates : (C.toLayered hwf).onlyUsesGates stdGateOps := by
  intro d u
  show (C.layerGate hwf d u).op ∈ stdGateOps
  unfold layerGate
  split
  · split
    · exact Or.inl (Or.inl rfl)
    · exact layerGateOf_mem _ _ _
  · exact Or.inl (Or.inl rfl)

/-- Every node of layer `m` evaluates to its vertex's value. -/
theorem toLayered_evalNode (hno : ∀ g ∈ C.gates, g.kind ≠ .or) (x : Fin n → Bool) :
    ∀ (m : ℕ) (hm : m ≤ C.gates.length) (u : C.layerNodes ⟨m, by omega⟩),
      (C.toLayered hwf).evalNode (d := ⟨m, by simp [toLayered]; omega⟩) u (fun i => b2f (x i)) =
        b2f ((C.values x).getD (C.ofNode hm u).val false)
  | 0, hm, u => by
    rw [evalNode_zero]
    have hval := C.values_getD_input x (C.ofNode hm u)
    simp only at hval
    rw [hval]
    rfl
  | m + 1, hm, u => by
    rw [evalNode_succ]
    show LayeredCircuit.Gate.eval (C.layerGate hwf ⟨m, by omega⟩ u) _ = _
    have hmG : m < C.gates.length := by omega
    have htgt := C.succ_le (d := ⟨m, by omega⟩) hmG
    have ih := toLayered_evalNode hno x m (by omega)
    unfold layerGate
    rw [dif_pos hmG]
    split
    · rename_i hu
      simp only [Gate.eval, Function.comp_def]
      rw [ih, ofNode_toNode]
    · rename_i hu
      have hv : (C.ofNode hm u).val = n + m := by
        have := (C.ofNode hm u).isLt
        have h' : ¬ (C.ofNode htgt u).val < n + m := hu
        simp only at this h' ⊢
        omega
      rw [hv, C.values_getD_gate x hmG]
      apply layerGateOf_eval _ _ (hno _ (List.getElem_mem hmG))
      intro a ha
      rw [ih, ofNode_toNode]

theorem toLayered_eval₁ (hno : ∀ g ∈ C.gates, g.kind ≠ .or) (x : Fin n → Bool) :
    (C.toLayered hwf).eval₁ (fun i => b2f (x i)) = b2f (C.eval x) := by
  have key : ∀ u : C.layerNodes ⟨C.gates.length + 1, by omega⟩,
      (C.toLayered hwf).evalNode (d := ⟨C.gates.length + 1, by simp [toLayered]⟩) u
        (fun i => b2f (x i)) = b2f (C.eval x) := by
    intro u
    rw [evalNode_succ]
    show LayeredCircuit.Gate.eval (C.layerGate hwf ⟨C.gates.length, by omega⟩ u) _ = _
    unfold layerGate
    rw [dif_neg (lt_irrefl _)]
    simp only [LayeredCircuit.Gate.eval, Function.comp_def]
    rw [C.toLayered_evalNode hwf hno x C.gates.length le_rfl, ofNode_toNode]
    rfl
  exact key _

/-- One gate per layer, each layer holding at most `size + 1` nodes. -/
theorem toLayered_size_le : (C.toLayered hwf).size ≤ (C.gates.length + 1) * (C.size + 1) := by
  unfold LayeredCircuit.size
  haveI : ∀ d : Fin (C.toLayered hwf).depth, Finite ((C.toLayered hwf).nodes d.succ) :=
    fun d => inferInstanceAs (Finite (C.layerNodes d.succ))
  rw [Nat.card_sigma]
  calc ∑ d : Fin (C.gates.length + 1), Nat.card (C.layerNodes d.succ)
      ≤ ∑ _d : Fin (C.gates.length + 1), (C.size + 1) := by
        apply Finset.sum_le_sum
        intro d _
        unfold layerNodes
        split
        · simp only [Nat.card_eq_fintype_card, Fintype.card_fin, DAGCircuit.size]
          rename_i h; simp only [Fin.val_succ] at h ⊢; omega
        · simp
    _ = (C.gates.length + 1) * (C.size + 1) := by simp

end ToLayered

end DAGCircuit

/-! ## Layered → DAG -/

/-- The shape of a gate of `stdGateOps`: a wire, a negation, or a conjunction. -/
inductive GateShape (D : Type) where
  | wire (a : D)
  | neg (a : D)
  | conj (as : List D)

/-- The value of a gate shape, in `Fin 2`. -/
def GateShape.eval {D : Type} (vals : D → Fin 2) : GateShape D → Fin 2
  | .wire a => vals a
  | .neg a => 1 - vals a
  | .conj as => (as.map vals).prod

theorem exists_gateShape {D : Type} (g : Gate (Fin 2) D) (h : g.op ∈ stdGateOps) :
    ∃ sh : GateShape D, ∀ vals, LayeredCircuit.Gate.eval g vals = sh.eval vals := by
  rcases g with ⟨op, inputs⟩
  simp only [stdGateOps, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_iUnion] at h
  rcases h with (rfl | rfl) | ⟨w, rfl⟩
  · exact ⟨.wire (inputs PUnit.unit), fun vals => rfl⟩
  · exact ⟨.neg (inputs 0), fun vals => rfl⟩
  · refine ⟨.conj (List.ofFn inputs), fun vals => ?_⟩
    simp only [LayeredCircuit.Gate.eval, GateShape.eval, Function.comp_def, List.map_ofFn]
    rw [List.prod_ofFn]

/-- The shape of a standard gate, chosen classically. -/
noncomputable def gateShape {D : Type} (g : Gate (Fin 2) D) (h : g.op ∈ stdGateOps) :
    GateShape D :=
  Classical.choose (exists_gateShape g h)

theorem gateShape_spec {D : Type} (g : Gate (Fin 2) D) (h : g.op ∈ stdGateOps) (vals : D → Fin 2) :
    LayeredCircuit.Gate.eval g vals = (gateShape g h).eval vals :=
  Classical.choose_spec (exists_gateShape g h) vals

theorem all_dedup' {l : List ℕ} (p : ℕ → Bool) : l.dedup.all p = l.all p := by
  rw [Bool.eq_iff_iff]; simp [List.all_eq_true, List.mem_dedup]

theorem b2f_all {α : Type} (l : List α) (f : α → Bool) :
    b2f (l.all f) = (l.map (b2f ∘ f)).prod := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.all_cons, b2f_and, ih]

namespace LayeredCircuit

variable {n : ℕ} (F : LayeredCircuit (Fin 2) (Fin n) Unit) (hfin : F.Finite)
  (hstd : F.onlyUsesGates stdGateOps)

/-- The number of nodes on layer `j + 1` (`0` past the last layer). -/
noncomputable def succCard (j : ℕ) : ℕ :=
  if h : j < F.depth then Nat.card (F.nodes (⟨j, h⟩ : Fin F.depth).succ) else 0

/-- The number of nodes on layers `1, …, m`: the DAG gates of those layers come first. -/
noncomputable def offset (m : ℕ) : ℕ := ∑ j ∈ Finset.range m, F.succCard j

theorem offset_succ (m : ℕ) : F.offset (m + 1) = F.offset m + F.succCard m :=
  Finset.sum_range_succ _ _

/-- An enumeration of layer `m`. -/
noncomputable def layerEnum (m : ℕ) (hm : m < F.depth + 1) :
    F.nodes ⟨m, hm⟩ ≃ Fin (Nat.card (F.nodes ⟨m, hm⟩)) :=
  haveI := hfin ⟨m, hm⟩
  _root_.Finite.equivFin _

/-- The DAG vertex of a node on layer `m`: an input for `m = 0`, otherwise the gate after
those of the earlier layers. -/
noncomputable def layerVertex : (m : ℕ) → (hm : m < F.depth + 1) → F.nodes ⟨m, hm⟩ → ℕ
  | 0, _, u => (F.nodes_zero ▸ u : Fin n).val
  | m + 1, hm, u => n + F.offset m + (F.layerEnum hfin (m + 1) hm u).val

/-- The DAG gate of a node on layer `m + 1`, from its gate's shape: a wire is a fan-in-one
`∧`, a negation a `¬`, a conjunction an `∧` over its (deduplicated) inputs. -/
noncomputable def layerGate (m : ℕ) (hm : m < F.depth) (u : F.nodes (⟨m, hm⟩ : Fin F.depth).succ) :
    DAGGate :=
  match gateShape (F.gates ⟨m, hm⟩ u) (hstd _ _) with
  | .wire a => ⟨.and, [F.layerVertex hfin m (by omega) a]⟩
  | .neg a => ⟨.not, [F.layerVertex hfin m (by omega) a]⟩
  | .conj as => ⟨.and, (as.map (F.layerVertex hfin m (by omega))).dedup⟩

/-- The DAG gates of layers `1, …, m`. -/
noncomputable def gatesUpTo : ℕ → List DAGGate
  | 0 => []
  | m + 1 => gatesUpTo m ++
      if h : m < F.depth then
        List.ofFn fun j : Fin (Nat.card (F.nodes (⟨m, h⟩ : Fin F.depth).succ)) =>
          F.layerGate hfin hstd m h ((F.layerEnum hfin (m + 1) (by omega)).symm j)
      else []

theorem length_gatesUpTo : ∀ m, (F.gatesUpTo hfin hstd m).length = F.offset m
  | 0 => by simp [gatesUpTo, offset]
  | m + 1 => by
    rw [gatesUpTo, List.length_append, length_gatesUpTo m, offset_succ, succCard]
    split <;> simp

theorem gatesUpTo_mono : ∀ {m M : ℕ}, m ≤ M →
    ∃ ext, F.gatesUpTo hfin hstd M = F.gatesUpTo hfin hstd m ++ ext
  | m, 0, h => ⟨[], by obtain rfl : m = 0 := (by omega); simp⟩
  | m, M + 1, h => by
    rcases Nat.lt_or_ge M m with hlt | hle
    · obtain rfl : m = M + 1 := by omega
      exact ⟨[], by simp⟩
    · obtain ⟨ext, hext⟩ := gatesUpTo_mono hle
      exact ⟨ext ++ _, by rw [gatesUpTo, hext, List.append_assoc]⟩

theorem layerVertex_lt : ∀ (m : ℕ) (hm : m < F.depth + 1) (u : F.nodes ⟨m, hm⟩),
    F.layerVertex hfin m hm u < n + F.offset m
  | 0, _, u => by simp [layerVertex, offset]
  | m + 1, hm, u => by
    have := (F.layerEnum hfin (m + 1) hm u).isLt
    rw [layerVertex, offset_succ, succCard, dif_pos (by omega)]
    have h2 : Nat.card (F.nodes (⟨m, by omega⟩ : Fin F.depth).succ) =
        Nat.card (F.nodes ⟨m + 1, hm⟩) := rfl
    omega

theorem layerVertex_ge (m : ℕ) (hm : m + 1 < F.depth + 1) (u : F.nodes ⟨m + 1, hm⟩) :
    n + F.offset m ≤ F.layerVertex hfin (m + 1) hm u := by
  simp [layerVertex]

/-- Gate `offset m + j` is the gate of the `j`-th node of layer `m + 1`. -/
theorem gatesUpTo_getElem (m : ℕ) (hm : m < F.depth) (u : F.nodes (⟨m, hm⟩ : Fin F.depth).succ)
    (h : F.offset m + (F.layerEnum hfin (m + 1) (by omega) u).val <
      (F.gatesUpTo hfin hstd (m + 1)).length) :
    (F.gatesUpTo hfin hstd (m + 1))[F.offset m + (F.layerEnum hfin (m + 1) (by omega) u).val] =
      F.layerGate hfin hstd m hm u := by
  simp only [gatesUpTo, dif_pos hm]
  rw [List.getElem_append_right (by rw [length_gatesUpTo]; omega)]
  simp only [List.getElem_ofFn]
  congr 1
  simp [length_gatesUpTo]

/-- The args of a layer-`(m + 1)` gate are layer-`m` vertices. -/
theorem layerGate_args_lt (m : ℕ) (hm : m < F.depth) (u : F.nodes (⟨m, hm⟩ : Fin F.depth).succ) :
    ∀ a ∈ (F.layerGate hfin hstd m hm u).args, a < n + F.offset m := by
  unfold layerGate
  split <;> intro a ha
  · simp at ha; subst ha; exact F.layerVertex_lt hfin _ _ _
  · simp at ha; subst ha; exact F.layerVertex_lt hfin _ _ _
  · obtain ⟨b, -, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp ha)
    exact F.layerVertex_lt hfin _ _ _

theorem layerGate_wellFormed (m : ℕ) (hm : m < F.depth) (u : F.nodes (⟨m, hm⟩ : Fin F.depth).succ) :
    (F.layerGate hfin hstd m hm u).WellFormed := by
  unfold layerGate
  split
  · exact ⟨List.nodup_singleton _, fun h => by simp at h⟩
  · exact ⟨List.nodup_singleton _, fun _ => rfl⟩
  · exact ⟨List.nodup_dedup _, fun h => by simp at h⟩

theorem gatesUpTo_acyclic : ∀ m, GatesAcyclic n (F.gatesUpTo hfin hstd m)
  | 0 => GatesAcyclic.nil
  | m + 1 => by
    intro i hi a ha
    by_cases hlt : i < (F.gatesUpTo hfin hstd m).length
    · have := gatesUpTo_acyclic m i hlt a
      simp only [gatesUpTo, List.getElem_append_left hlt] at ha
      exact this ha
    · have hm : m < F.depth := by
        by_contra hm
        simp only [gatesUpTo, dif_neg hm, List.append_nil] at hi
        exact hlt hi
      simp only [gatesUpTo, dif_pos hm, List.getElem_append_right (Nat.le_of_not_lt hlt),
        List.getElem_ofFn] at ha
      have := F.layerGate_args_lt hfin hstd m hm _ a ha
      rw [length_gatesUpTo] at hlt
      omega

/-- Every node of layer `m` is computed, in `Fin 2`, by its DAG vertex. -/
theorem layerVertex_value (x : Fin n → Bool) :
    ∀ (m : ℕ) (hm : m < F.depth + 1) (u : F.nodes ⟨m, hm⟩),
      b2f (vertexValue (F.gatesUpTo hfin hstd m) x (F.layerVertex hfin m hm u)) =
        F.evalNode u (fun i => b2f (x i))
  | 0, hm, u => by
    rw [evalNode_zero]
    simp only [layerVertex, gatesUpTo]
    rw [vertexValue_input [] x (F.nodes_zero ▸ u)]
  | m + 1, hm, u => by
    have hmd : m < F.depth := by omega
    rw [evalNode_succ, gateShape_spec _ (hstd _ _)]
    set j := (F.layerEnum hfin (m + 1) hm u).val with hj
    have hlen : F.offset m + j < (F.gatesUpTo hfin hstd (m + 1)).length := by
      rw [length_gatesUpTo, offset_succ, succCard, dif_pos hmd]
      exact Nat.add_lt_add_left (F.layerEnum hfin (m + 1) hm u).isLt _
    have hval := runWith_getD_gate DAGGate.eval (F.gatesUpTo hfin hstd (m + 1))
      (List.ofFn x) hlen false
    rw [List.length_ofFn] at hval
    have hgate := F.gatesUpTo_getElem hfin hstd m hmd u hlen
    rw [hgate] at hval
    have hlv : F.layerVertex hfin (m + 1) hm u = n + (F.offset m + j) := by
      simp [layerVertex, hj]; omega
    rw [hlv]
    show b2f ((runWith DAGGate.eval (F.gatesUpTo hfin hstd (m + 1)) (List.ofFn x)).getD
      (n + (F.offset m + j)) false) = _
    rw [hval]
    -- the gate reads only layer-`m` vertices, whose values are those of `gatesUpTo m`
    obtain ⟨ext, hprefix⟩ := F.gatesUpTo_mono hfin hstd (Nat.le_succ m)
    have hread : ∀ a ∈ (F.layerGate hfin hstd m hmd u).args,
        (runWith DAGGate.eval ((F.gatesUpTo hfin hstd (m + 1)).take (F.offset m + j))
          (List.ofFn x)).getD a false = vertexValue (F.gatesUpTo hfin hstd m) x a := by
      intro a ha
      have ha' := F.layerGate_args_lt hfin hstd m hmd u a ha
      rw [runWith_getD_take _ _ _ (by omega) (by simpa using by omega)]
      rw [hprefix]
      exact vertexValue_append _ _ _ (by rw [length_gatesUpTo]; exact ha')
    rw [DAGGate.eval_congr _ hread]
    have ih := layerVertex_value x m (by omega)
    unfold layerGate
    split
    · rename_i a heq
      simp only [heq, GateShape.eval, DAGGate.eval, List.all_cons, List.all_nil, Bool.and_true]
      exact ih a
    · rename_i a heq
      simp only [heq, GateShape.eval, DAGGate.eval, List.all_cons, List.all_nil, Bool.and_true]
      rw [b2f_not, ← ih a]; rfl
    · rename_i as heq
      simp only [heq, GateShape.eval, DAGGate.eval]
      rw [all_dedup', List.all_map, b2f_all]
      congr 1
      exact List.map_congr_left fun a _ => ih a

/-- A finite layered circuit over `stdGateOps` as a DAG circuit, one gate per non-input
node. -/
noncomputable def toDAG : DAGCircuit n where
  gates := F.gatesUpTo hfin hstd F.depth
  output := F.layerVertex hfin F.depth (Nat.lt_succ_self _) (F.nodes_last.symm ▸ ())
  args_lt := F.gatesUpTo_acyclic hfin hstd F.depth
  output_lt := by
    rw [length_gatesUpTo]; exact F.layerVertex_lt hfin _ _ _

theorem toDAG_eval (x : Fin n → Bool) :
    b2f ((F.toDAG hfin hstd).eval x) = F.eval₁ (fun i => b2f (x i)) := by
  exact F.layerVertex_value hfin hstd x F.depth (Nat.lt_succ_self _) _

/-- The DAG has `n` input vertices and one gate per non-input node. -/
theorem toDAG_size : (F.toDAG hfin hstd).size = n + F.size := by
  simp only [DAGCircuit.size, toDAG, length_gatesUpTo, offset, LayeredCircuit.size]
  haveI : ∀ d : Fin F.depth, _root_.Finite (F.nodes d.succ) := fun d => hfin d.succ
  rw [Nat.card_sigma, ← Fin.sum_univ_eq_sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  simp [succCard, d.isLt]

theorem gatesUpTo_wellFormed : ∀ M, ∀ g ∈ F.gatesUpTo hfin hstd M, g.WellFormed
  | 0 => by simp [gatesUpTo]
  | M + 1 => by
    intro g hg
    rw [gatesUpTo, List.mem_append] at hg
    rcases hg with hg | hg
    · exact gatesUpTo_wellFormed M g hg
    · split at hg
      · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
        exact F.layerGate_wellFormed hfin hstd M _ _
      · simp at hg

theorem toDAG_isWellFormed : (F.toDAG hfin hstd).IsWellFormed :=
  fun g hg => F.gatesUpTo_wellFormed hfin hstd _ g hg

end LayeredCircuit

/-! ## Tree circuits as layered circuits, gate by gate -/

namespace TreeCircuit

variable {n : ℕ} (c : TreeCircuit n)

/-- A tree circuit as a layered circuit over `stdGateOps`, built gate by gate (compile to a
DAG, remove `∨` by De Morgan, layer).  Unlike the semantic wrapper `toLayeredWrapper`, every
gate is a standard gate and the size is polynomial in `c.size`. -/
def toLayered : LayeredCircuit (Fin 2) (Fin n) Unit :=
  (c.toDAG.deMorgan c.toDAG_isWellFormed).toLayered
    (c.toDAG.deMorgan_isWellFormed c.toDAG_isWellFormed)

theorem toLayered_eval₁ (x : Fin n → Bool) :
    c.toLayered.eval₁ (fun i => b2f (x i)) = b2f (c.eval x) := by
  rw [toLayered, DAGCircuit.toLayered_eval₁ _ _ (DAGCircuit.deMorgan_kind_ne_or _ _),
    DAGCircuit.deMorgan_eval, toDAG_eval]

theorem toLayered_finite : c.toLayered.Finite := DAGCircuit.toLayered_finite _ _

theorem toLayered_onlyUsesGates : c.toLayered.onlyUsesGates stdGateOps :=
  DAGCircuit.toLayered_onlyUsesGates _ _

end TreeCircuit

/-! ## The two `P/poly`s coincide -/

/-- `size * (size + 2)` bounds both rewriting passes. -/
private theorem rewrite_size_le {n G S T : ℕ} (hS : S = n + G) (h : T ≤ n + G * (S + 2)) :
    T ≤ S * (S + 2) := by
  subst hS; nlinarith

/-- A polynomial-size layered family gives a polynomial-size fan-in-two DAG family: one gate
per node, then binarization. -/
theorem _root_.Language.InLayeredPPoly.inPPoly {L : Language Bool} (h : L.InLayeredPPoly) :
    L.InPPoly := by
  obtain ⟨C, hstd, ⟨a, k, hs⟩, hL⟩ := (Language.inLayeredPPoly_iff L).mp h
  set D : (n : ℕ) → DAGCircuit n := fun n => (C.circuit n).toDAG (C.finite n) (hstd n) with hD
  have hwf : ∀ n, (D n).IsWellFormed := fun n => (C.circuit n).toDAG_isWellFormed _ _
  refine (Language.inPPoly_iff L).mpr ⟨⟨fun n => (D n).binarize (hwf n)⟩,
    fun n => (D n).binarize_isFaninTwo (hwf n), ⟨3 * (a + 1) ^ 2, 2 * (k + 1), fun n => ?_⟩, ?_⟩
  · have hP : (D n).size ≤ (a + 1) * (n + 1) ^ (k + 1) := by
      rw [hD, LayeredCircuit.toDAG_size]
      have h1 : n + 1 ≤ (n + 1) ^ (k + 1) := Nat.le_self_pow (by omega) _
      have h2 : (n + 1) ^ k ≤ (n + 1) ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have := hs n
      nlinarith
    have hpos : 1 ≤ (a + 1) * (n + 1) ^ (k + 1) :=
      Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hb := rewrite_size_le rfl ((D n).binarize_size_le (hwf n))
    calc ((D n).binarize (hwf n)).size ≤ (D n).size * ((D n).size + 2) := hb
      _ ≤ ((a + 1) * (n + 1) ^ (k + 1)) * (3 * ((a + 1) * (n + 1) ^ (k + 1))) :=
          Nat.mul_le_mul hP (by omega)
      _ = 3 * (a + 1) ^ 2 * (n + 1) ^ (2 * (k + 1)) := by ring
  · rw [← hL]; ext w
    simp only [DAGCircuitFamily.mem_language_iff, LayeredCircuitFamily.mem_language_iff,
      DAGCircuit.binarize_eval]
    rw [← b2f_eq_one_iff, hD]
    exact Eq.congr_left (LayeredCircuit.toDAG_eval _ _ _ _)

/-- A polynomial-size fan-in-two DAG family gives a polynomial-size layered family over
`stdGateOps`: De Morgan, then one gate per layer. -/
theorem _root_.Language.InPPoly.inLayeredPPoly {L : Language Bool} (h : L.InPPoly) :
    L.InLayeredPPoly := by
  obtain ⟨C, hF, ⟨a, k, hs⟩, hL⟩ := (Language.inPPoly_iff L).mp h
  have hwf : C.IsWellFormed := hF.isWellFormed
  set E : (n : ℕ) → DAGCircuit n := fun n => (C.circuit n).deMorgan (hwf n) with hE
  have hwfE : ∀ n, (E n).IsWellFormed := fun n => DAGCircuit.deMorgan_isWellFormed _ _
  refine (Language.inLayeredPPoly_iff L).mpr ⟨⟨fun n => (E n).toLayered (hwfE n),
    fun n => DAGCircuit.toLayered_finite _ _⟩, fun n => DAGCircuit.toLayered_onlyUsesGates _ _,
    ⟨(a + 1) ^ 4, 4 * k, fun n => ?_⟩, ?_⟩
  · set S := (C.circuit n).size with hSdef
    have hES : (E n).size ≤ S * (S + 2) :=
      rewrite_size_le rfl (DAGCircuit.deMorgan_size_le _ _)
    have hG : (E n).gates.length ≤ (E n).size := by simp [DAGCircuit.size]
    have hS : S + 1 ≤ (a + 1) * (n + 1) ^ k := by
      have := hs n
      have : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (by omega)
      nlinarith
    show ((E n).toLayered (hwfE n)).size ≤ _
    calc ((E n).toLayered (hwfE n)).size ≤ ((E n).gates.length + 1) * ((E n).size + 1) :=
          DAGCircuit.toLayered_size_le _ _
      _ ≤ ((S + 1) ^ 2) * ((S + 1) ^ 2) := by
          apply Nat.mul_le_mul <;> nlinarith
      _ = (S + 1) ^ 4 := by ring
      _ ≤ ((a + 1) * (n + 1) ^ k) ^ 4 := Nat.pow_le_pow_left hS 4
      _ = (a + 1) ^ 4 * (n + 1) ^ (4 * k) := by ring
  · rw [← hL]; ext w
    simp only [DAGCircuitFamily.mem_language_iff, LayeredCircuitFamily.mem_language_iff]
    rw [← b2f_eq_one_iff, ← DAGCircuit.deMorgan_eval _ (hwf _)]
    exact Eq.congr_left (DAGCircuit.toLayered_eval₁ _ _ (DAGCircuit.deMorgan_kind_ne_or _ _) _)

/-- The book's `P/poly` (fan-in-two DAGs) is the layered model's `P/poly`. -/
theorem _root_.Language.inPPoly_iff_inLayeredPPoly (L : Language Bool) :
    L.InPPoly ↔ L.InLayeredPPoly :=
  ⟨Language.InPPoly.inLayeredPPoly, Language.InLayeredPPoly.inPPoly⟩

theorem PPoly_eq_LayeredPPoly : PPoly = LayeredPPoly := by
  ext L; exact Language.inPPoly_iff_inLayeredPPoly L

end BoolCircuit
