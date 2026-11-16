/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.DAGCircuit
import TCSlib.Complexity.CircuitComplexity.Basic

/-!
# Converting between tree circuits and DAG circuits

`BoolCircuit.TreeCircuit` (a formula: fan-out one, unbounded fan-in, negation only at the
inputs) and `BoolCircuit.DAGCircuit` ([AB09, Def 6.1]) are related in both directions.

* **Tree → DAG** (`BoolCircuit.TreeCircuit.toDAG`) compiles each internal node to one gate
  and each negative literal to a `¬` gate; a positive literal is its input vertex.  It is
  linear: the DAG has at most `n + c.size` vertices and depth at most `c.depth + 1`, and
  fan-in at most two is preserved.
* **DAG → Tree** (`BoolCircuit.DAGCircuit.toTree`) unfolds the DAG from the output,
  duplicating every shared vertex and pushing negations to the inputs by De Morgan.  Depth
  does not grow, but size grows to at most `(k + 1) ^ depth` for fan-in `k`; this blowup is
  unavoidable in general, and is polynomial exactly in the regimes `NC¹` and `AC⁰` use.

## Main definitions

* `BoolCircuit.TreeCircuit.toDAG` — the linear compilation.
* `BoolCircuit.DAGCircuit.toTree` — the unfolding.

## Main results

* `BoolCircuit.TreeCircuit.toDAG_eval`, `toDAG_size_le`, `toDAG_depth_le`,
  `toDAG_isWellFormed`, `toDAG_isFaninTwo`.
* `BoolCircuit.DAGCircuit.toTree_eval`, `toTree_size_le`, `toTree_depth_le`,
  `toTree_maxFanin_le`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1; formulas as fan-out-one circuits.)
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

variable {n : ℕ}

/-! ## Vertex values and depths of a gate list -/

/-- The value of vertex `v` after running `gs` on input `x`. -/
def vertexValue (gs : List DAGGate) (x : Fin n → Bool) (v : ℕ) : Bool :=
  (runWith DAGGate.eval gs (List.ofFn x)).getD v false

/-- The depth of vertex `v` after running `gs` over `n` inputs. -/
def vertexDepth (n : ℕ) (gs : List DAGGate) (v : ℕ) : ℕ :=
  (runWith DAGGate.depth gs (List.replicate n 0)).getD v 0

/-- Appending gates does not change the value of an existing vertex: if `v` is below
`n + gs.length` (an input or a gate of `gs`), its value under `gs ++ ext` equals its value
under `gs`. -/
theorem vertexValue_append (gs ext : List DAGGate) (x : Fin n → Bool) {v : ℕ}
    (hv : v < n + gs.length) : vertexValue (gs ++ ext) x v = vertexValue gs x v := by
  unfold vertexValue
  rw [runWith_append, runWith_getD_of_lt]
  simpa using hv

/-- Appending gates does not change the depth of an existing vertex: if
`v < n + gs.length`, its depth under `gs ++ ext` equals its depth under `gs`. -/
theorem vertexDepth_append (gs ext : List DAGGate) {v : ℕ} (hv : v < n + gs.length) :
    vertexDepth n (gs ++ ext) v = vertexDepth n gs v := by
  unfold vertexDepth
  rw [runWith_append, runWith_getD_of_lt]
  simpa using hv

/-- The value of the newly appended last vertex `n + gs.length` of `gs ++ [g]` is the
gate `g` evaluated on the vertex values produced by `gs`. -/
theorem vertexValue_last (gs : List DAGGate) (g : DAGGate) (x : Fin n → Bool) :
    vertexValue (gs ++ [g]) x (n + gs.length) =
      g.eval (runWith DAGGate.eval gs (List.ofFn x)) := by
  have := runWith_getD_last DAGGate.eval gs g (List.ofFn x) false
  simpa [vertexValue] using this

/-- The depth of the newly appended last vertex `n + gs.length` of `gs ++ [g]` is the
depth of `g` computed from the vertex depths produced by `gs` (one more than the
deepest vertex it reads). -/
theorem vertexDepth_last (gs : List DAGGate) (g : DAGGate) :
    vertexDepth n (gs ++ [g]) (n + gs.length) =
      g.depth (runWith DAGGate.depth gs (List.replicate n 0)) := by
  have := runWith_getD_last DAGGate.depth gs g (List.replicate n 0) 0
  simpa [vertexDepth] using this

/-- The value of input vertex `i < n` is the input bit `x i`, whatever gates follow. -/
theorem vertexValue_input (gs : List DAGGate) (x : Fin n → Bool) (i : Fin n) :
    vertexValue gs x i = x i := by
  unfold vertexValue
  rw [runWith_getD_of_lt _ _ _ (by simp)]
  simp

/-- Every input vertex `i < n` has depth `0`, whatever gates follow. -/
theorem vertexDepth_input (gs : List DAGGate) {i : ℕ} (hi : i < n) :
    vertexDepth n gs i = 0 := by
  unfold vertexDepth
  rw [runWith_getD_of_lt _ _ _ (by simpa using hi)]
  simp [hi]

/-! ## Small list facts -/

private theorem all_dedup {l : List ℕ} (p : ℕ → Bool) : l.dedup.all p = l.all p := by
  rw [Bool.eq_iff_iff]; simp [List.all_eq_true, List.mem_dedup]

private theorem any_dedup {l : List ℕ} (p : ℕ → Bool) : l.dedup.any p = l.any p := by
  rw [Bool.eq_iff_iff]; simp [List.any_eq_true, List.mem_dedup]

private theorem foldr_max_le {l : List ℕ} {f : ℕ → ℕ} {B : ℕ} (h : ∀ a ∈ l, f a ≤ B) :
    (l.map f).foldr max 0 ≤ B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

/-- An `∧`-node of a tree circuit evaluates to the conjunction (`List.all`) of its
children's values. -/
theorem TreeCircuit.eval_node_true (cs : List (TreeCircuit n)) (x : Fin n → Bool) :
    (TreeCircuit.node true cs).eval x = cs.all fun c => c.eval x := by
  rw [Bool.eq_iff_iff, TreeCircuit.eval_node_true_iff]; simp [List.all_eq_true]

/-- An `∨`-node of a tree circuit evaluates to the disjunction (`List.any`) of its
children's values. -/
theorem TreeCircuit.eval_node_false (cs : List (TreeCircuit n)) (x : Fin n → Bool) :
    (TreeCircuit.node false cs).eval x = cs.any fun c => c.eval x := by
  rw [Bool.eq_iff_iff, TreeCircuit.eval_node_false_iff]; simp [List.any_eq_true]

/-! ## Tree → DAG -/

/-- The `∧`/`∨` label of a tree node. -/
def nodeKind (isAnd : Bool) : GateKind := if isAnd then .and else .or

mutual
/-- Compile `c` after the gates `gs`: returns the extended gate list and the vertex that
holds `c`'s value.  A positive literal is its input vertex; a negative literal gets a `¬`
gate; a node gets one gate over its children's (deduplicated) vertices. -/
def compileTree (n : ℕ) : TreeCircuit n → List DAGGate → List DAGGate × ℕ
  | .lit l, gs =>
    if l.sign then (gs, l.idx) else (gs ++ [⟨.not, [l.idx]⟩], n + gs.length)
  | .node b cs, gs =>
    let r := compileTrees n cs gs
    (r.1 ++ [⟨nodeKind b, r.2.dedup⟩], n + r.1.length)

/-- Compile a list of circuits one after another. -/
def compileTrees (n : ℕ) : List (TreeCircuit n) → List DAGGate → List DAGGate × List ℕ
  | [], gs => (gs, [])
  | c :: cs, gs =>
    let r := compileTree n c gs
    let r' := compileTrees n cs r.1
    (r'.1, r.2 :: r'.2)
end

/-- What compiling one circuit guarantees. -/
structure CompileSpec (n : ℕ) (c : TreeCircuit n) (gs : List DAGGate)
    (r : List DAGGate × ℕ) : Prop where
  extends_gates : ∃ ext, r.1 = gs ++ ext
  acyclic : GatesAcyclic n r.1
  vertex_lt : r.2 < n + r.1.length
  value : ∀ x, vertexValue r.1 x r.2 = c.eval x
  length_le : r.1.length ≤ gs.length + c.size
  depth_le : vertexDepth n r.1 r.2 ≤ c.depth + 1
  new_gates : ∀ g ∈ r.1.drop gs.length, g.WellFormed ∧ g.args.length ≤ max 1 c.maxFanin

/-- What compiling a list of circuits guarantees. -/
structure CompileListSpec (n : ℕ) (cs : List (TreeCircuit n)) (gs : List DAGGate)
    (r : List DAGGate × List ℕ) : Prop where
  extends_gates : ∃ ext, r.1 = gs ++ ext
  acyclic : GatesAcyclic n r.1
  length_eq : r.2.length = cs.length
  vertex_lt : ∀ v ∈ r.2, v < n + r.1.length
  value : ∀ x, r.2.map (vertexValue r.1 x) = cs.map fun c => c.eval x
  length_le : r.1.length ≤ gs.length + TreeCircuit.sumSize cs
  depth_le : ∀ v ∈ r.2, vertexDepth n r.1 v ≤ TreeCircuit.maxDepth cs + 1
  new_gates : ∀ g ∈ r.1.drop gs.length,
    g.WellFormed ∧ g.args.length ≤ max 1 (TreeCircuit.maxFaninL cs)

private theorem drop_append_of_prefix {gs ext : List DAGGate} :
    (gs ++ ext).drop gs.length = ext := by simp

/-- Correctness of compiling a list of tree circuits: if each circuit `c` in `cs`
compiles correctly after any acyclic gate list (the `CompileSpec` invariants), then
compiling `cs` in sequence after an acyclic `gs` meets `CompileListSpec`: it extends `gs`,
stays acyclic, returns one in-range vertex per circuit holding that circuit's value, adds
at most `sumSize cs` gates, each returned vertex has depth at most `maxDepth cs + 1`, and
every new gate is well-formed with fan-in at most `max 1 (maxFaninL cs)`.

**Proof sketch.** Induction on the list.  The empty list returns `gs` unchanged and no
vertices.  For `c :: cs`, compile `c` after `gs` (hypothesis for `c`) and then `cs` after
the result (induction hypothesis).  The second stage only appends gates, so the vertex
for `c` keeps its value and depth (values/depths of existing vertices are stable under
appending); the gate-count, depth and fan-in bounds add up or take maxima, matching
`sumSize`, `maxDepth` and `maxFaninL` of the cons. -/
theorem compileTrees_spec :
    ∀ (cs : List (TreeCircuit n)),
      (∀ c ∈ cs, ∀ gs, GatesAcyclic n gs → CompileSpec n c gs (compileTree n c gs)) →
      ∀ gs, GatesAcyclic n gs → CompileListSpec n cs gs (compileTrees n cs gs)
  | [], _, gs, hgs => by
    refine ⟨⟨[], by simp [compileTrees]⟩, by simpa [compileTrees] using hgs, by simp [compileTrees],
      by simp [compileTrees], fun x => by simp [compileTrees],
      by simp [compileTrees, TreeCircuit.sumSize_nil], by simp [compileTrees], ?_⟩
    simp [compileTrees]
  | c :: cs, ih, gs, hgs => by
    have h1 := ih c (by simp) gs hgs
    set r1 := compileTree n c gs with hr1
    have h2 := compileTrees_spec cs (fun c' hc' => ih c' (by simp [hc'])) r1.1 h1.acyclic
    set r2 := compileTrees n cs r1.1 with hr2
    have hres : compileTrees n (c :: cs) gs = (r2.1, r1.2 :: r2.2) := by
      simp [compileTrees, hr1, hr2]
    rw [hres]
    obtain ⟨e1, he1⟩ := h1.extends_gates
    obtain ⟨e2, he2⟩ := h2.extends_gates
    have hlen12 : r1.1.length ≤ r2.1.length := by rw [he2]; simp
    refine ⟨⟨e1 ++ e2, by rw [he2, he1, List.append_assoc]⟩, h2.acyclic,
      by simp [h2.length_eq], ?_, ?_, ?_, ?_, ?_⟩
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · show r1.2 < n + r2.1.length
        exact lt_of_lt_of_le h1.vertex_lt (by omega)
      · exact h2.vertex_lt v hv
    · intro x
      simp only [List.map_cons]
      rw [h2.value x, he2, vertexValue_append _ _ _ h1.vertex_lt, h1.value x]
    · show r2.1.length ≤ gs.length + TreeCircuit.sumSize (c :: cs)
      have := h1.length_le; have := h2.length_le
      rw [TreeCircuit.sumSize_cons]; omega
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · rw [he2, vertexDepth_append _ _ h1.vertex_lt]
        exact h1.depth_le.trans (by rw [TreeCircuit.maxDepth_cons]; omega)
      · exact (h2.depth_le v hv).trans (by rw [TreeCircuit.maxDepth_cons]; omega)
    · intro g hg
      have hsplit : r2.1.drop gs.length = e1 ++ e2 := by
        rw [he2, he1, List.append_assoc]; simp
      rw [hsplit, List.mem_append] at hg
      rcases hg with hg | hg
      · have := h1.new_gates g (by rw [he1]; simpa using hg)
        exact ⟨this.1, this.2.trans (by rw [TreeCircuit.maxFaninL_cons]; omega)⟩
      · have := h2.new_gates g (by rw [he2]; simpa using hg)
        exact ⟨this.1, this.2.trans (by rw [TreeCircuit.maxFaninL_cons]; omega)⟩

/-- Correctness of compiling one tree circuit: compiling `c` after an acyclic gate list
`gs` yields an acyclic extension of `gs` and an in-range vertex that computes `c`, with
at most `c.size` new gates, vertex depth at most `c.depth + 1`, and every new gate
well-formed with fan-in at most `max 1 c.maxFanin` (the `CompileSpec` invariants).

**Proof sketch.** Structural induction on `c`.  A positive literal returns its input
vertex and adds nothing.  A negative literal appends one `¬` gate on its input vertex,
of depth `1` and value the negated input.  A node first compiles its children (by
`compileTrees_spec` and the induction hypothesis), then appends one `∧`/`∨` gate over
the deduplicated child vertices: deduplication does not change `all`/`any`, so the gate
computes the node's value; its depth is one more than the deepest child vertex, at most
`maxDepth + 2 = depth + 1`; its fan-in is at most the number of children. -/
theorem compileTree_spec (c : TreeCircuit n) :
    ∀ gs, GatesAcyclic n gs → CompileSpec n c gs (compileTree n c gs) := by
  induction c using TreeCircuit.ind with
  | hlit l =>
    intro gs hgs
    rcases l with ⟨i, s⟩
    cases s
    · -- a negative literal: one `¬` gate
      have hres : compileTree n (.lit ⟨i, false⟩) gs = (gs ++ [⟨.not, [i]⟩], n + gs.length) := by
        simp [compileTree]
      rw [hres]
      refine ⟨⟨_, rfl⟩, hgs.snoc ?_, by simp, fun x => ?_, by simp [TreeCircuit.size],
        ?_, ?_⟩
      · intro a ha
        simp only [List.mem_singleton] at ha
        subst ha; have := i.isLt; omega
      · rw [vertexValue_last]
        have hin := vertexValue_input gs x i
        simp only [vertexValue] at hin
        simp [DAGGate.eval, TreeCircuit.eval, Lit.eval]
        simpa using hin
      · rw [vertexDepth_last]
        have hin := vertexDepth_input (n := n) gs i.isLt
        simp only [vertexDepth] at hin
        simp [DAGGate.depth, TreeCircuit.depth]
        simpa using hin
      · intro g hg
        simp only [drop_append_of_prefix, List.mem_singleton] at hg
        subst hg
        exact ⟨⟨List.nodup_singleton _, fun _ => rfl⟩, by simp⟩
    · -- a positive literal: its input vertex
      have hres : compileTree n (.lit ⟨i, true⟩) gs = (gs, (i : ℕ)) := by simp [compileTree]
      rw [hres]
      refine ⟨⟨[], by simp⟩, hgs, by omega, fun x => ?_, by simp [TreeCircuit.size], ?_, ?_⟩
      · rw [vertexValue_input]; simp [TreeCircuit.eval, Lit.eval]
      · rw [vertexDepth_input _ i.isLt]; simp [TreeCircuit.depth]
      · simp
  | hnode b cs ih =>
    intro gs hgs
    have h := compileTrees_spec cs ih gs hgs
    set r := compileTrees n cs gs with hr
    set g : DAGGate := ⟨nodeKind b, r.2.dedup⟩ with hg
    have hres : compileTree n (.node b cs) gs = (r.1 ++ [g], n + r.1.length) := by
      rw [compileTree]
    rw [hres]
    obtain ⟨e, he⟩ := h.extends_gates
    refine ⟨⟨e ++ [g], by rw [he, List.append_assoc]⟩, h.acyclic.snoc ?_, by simp, ?_, ?_, ?_, ?_⟩
    · intro a ha
      exact h.vertex_lt a (List.mem_dedup.mp ha)
    · intro x
      rw [vertexValue_last]
      have hv : ∀ p : Bool → Bool → Bool, True := fun _ => trivial
      have hall : (r.2.all fun a => (runWith DAGGate.eval r.1 (List.ofFn x)).getD a false) =
          cs.all fun c => c.eval x := by
        have := congrArg (fun l => l.all id) (h.value x)
        simpa [List.all_map, Function.comp_def, vertexValue] using this
      have hany : (r.2.any fun a => (runWith DAGGate.eval r.1 (List.ofFn x)).getD a false) =
          cs.any fun c => c.eval x := by
        have := congrArg (fun l => l.any id) (h.value x)
        simpa [List.any_map, Function.comp_def, vertexValue] using this
      cases b
      · simp only [hg, DAGGate.eval, nodeKind, Bool.false_eq_true, if_false]
        rw [any_dedup, hany, TreeCircuit.eval_node_false]
      · simp only [hg, DAGGate.eval, nodeKind, if_true]
        rw [all_dedup, hall, TreeCircuit.eval_node_true]
    · have := h.length_le
      simp [TreeCircuit.size_node]; omega
    · rw [vertexDepth_last, TreeCircuit.depth_node]
      simp only [hg, DAGGate.depth]
      have : ((r.2.dedup).map fun a =>
          (runWith DAGGate.depth r.1 (List.replicate n 0)).getD a 0).foldr max 0 ≤
            TreeCircuit.maxDepth cs + 1 :=
        foldr_max_le fun a ha => h.depth_le a (List.mem_dedup.mp ha)
      omega
    · intro g' hg'
      have hsplit : (r.1 ++ [g]).drop gs.length = e ++ [g] := by
        rw [he, List.append_assoc]; simp
      rw [hsplit, List.mem_append, List.mem_singleton] at hg'
      rcases hg' with hg' | rfl
      · have := h.new_gates g' (by rw [he]; simpa using hg')
        exact ⟨this.1, this.2.trans (by rw [TreeCircuit.maxFanin_node]; omega)⟩
      · refine ⟨⟨List.nodup_dedup _, fun hk => ?_⟩, ?_⟩
        · cases b <;> simp [hg, nodeKind] at hk
        · have : r.2.dedup.length ≤ cs.length :=
            (List.dedup_sublist _).length_le.trans h.length_eq.le
          rw [TreeCircuit.maxFanin_node]; simp only [hg]; omega

/-- Compile a tree circuit to a DAG circuit.  Linear: see `toDAG_size_le`. -/
def TreeCircuit.toDAG (c : TreeCircuit n) : DAGCircuit n where
  gates := (compileTree n c []).1
  output := (compileTree n c []).2
  args_lt := (compileTree_spec c [] GatesAcyclic.nil).acyclic
  output_lt := (compileTree_spec c [] GatesAcyclic.nil).vertex_lt

/-- The DAG compiled from a tree circuit computes the same Boolean function: for every
input `x`, `c.toDAG.eval x = c.eval x`. -/
theorem TreeCircuit.toDAG_eval (c : TreeCircuit n) (x : Fin n → Bool) :
    c.toDAG.eval x = c.eval x :=
  (compileTree_spec c [] GatesAcyclic.nil).value x

/-- The DAG has at most `n + c.size` vertices: `n` inputs and at most one gate per
tree node. -/
theorem TreeCircuit.toDAG_size_le (c : TreeCircuit n) : c.toDAG.size ≤ n + c.size := by
  have := (compileTree_spec c [] GatesAcyclic.nil).length_le
  simp only [DAGCircuit.size, TreeCircuit.toDAG]; simpa using this

/-- Depth grows by at most one, for the `¬` gates at negative literals. -/
theorem TreeCircuit.toDAG_depth_le (c : TreeCircuit n) : c.toDAG.depth ≤ c.depth + 1 :=
  (compileTree_spec c [] GatesAcyclic.nil).depth_le

/-- The DAG compiled from a tree circuit is well-formed: every gate has duplicate-free
arguments and every `¬` gate reads exactly one vertex. -/
theorem TreeCircuit.toDAG_isWellFormed (c : TreeCircuit n) : c.toDAG.IsWellFormed := by
  intro g hg
  exact ((compileTree_spec c [] GatesAcyclic.nil).new_gates g (by simpa using hg)).1

/-- A fan-in-two tree compiles to a fan-in-two DAG. -/
theorem TreeCircuit.toDAG_isFaninTwo (c : TreeCircuit n) (hc : c.maxFanin ≤ 2) :
    c.toDAG.IsFaninTwo := by
  refine ⟨c.toDAG_isWellFormed, fun g hg => ?_⟩
  have := ((compileTree_spec c [] GatesAcyclic.nil).new_gates g (by simpa using hg)).2
  omega

/-! ## DAG → Tree -/

/-- Unfold one gate whose inputs unfold by `t`, at polarity `pos`: `¬` flips the
polarity, and a negated `∧` (`∨`) becomes an `∨` (`∧`) of negated children (De Morgan). -/
def unfoldGate (g : DAGGate) (t : ℕ → Bool → TreeCircuit n) (pos : Bool) : TreeCircuit n :=
  match g.kind with
  | .and => .node pos (g.args.map fun a => t a pos)
  | .or => .node (!pos) (g.args.map fun a => t a pos)
  | .not => t (g.args.headD 0) (!pos)

/-- Unfold vertex `v` of the gates `gs` (over `n` inputs) into a tree computing its value
(`pos = true`) or its negation (`pos = false`), so that negations end at the inputs.
`fuel` bounds the recursion; `fuel > v` always suffices. -/
def unfoldVertex (n : ℕ) (gs : List DAGGate) : ℕ → ℕ → Bool → TreeCircuit n
  | 0, _, _ => .node true []
  | fuel + 1, v, pos =>
    if h : v < n then .lit ⟨⟨v, h⟩, pos⟩
    else unfoldGate (gs.getD (v - n) (constGate true)) (unfoldVertex n gs fuel) pos

/-- Unfold a DAG circuit into a tree circuit, from its output. -/
def DAGCircuit.toTree (C : DAGCircuit n) : TreeCircuit n :=
  unfoldVertex n C.gates (C.output + 1) C.output true

private theorem maxDepth_map {α : Type} (l : List α) (f : α → TreeCircuit n) :
    TreeCircuit.maxDepth (l.map f) = (l.map fun a => (f a).depth).foldr max 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [TreeCircuit.maxDepth_cons, ih]

/-- The total size of a mapped list of trees is the sum of the mapped sizes. -/
theorem sumSize_map {α : Type} (l : List α) (f : α → TreeCircuit n) :
    TreeCircuit.sumSize (l.map f) = (l.map fun a => (f a).size).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [TreeCircuit.sumSize_cons, ih]

private theorem maxFaninL_map {α : Type} (l : List α) (f : α → TreeCircuit n) :
    TreeCircuit.maxFaninL (l.map f) = (l.map fun a => (f a).maxFanin).foldr max 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [TreeCircuit.maxFaninL_cons, ih]

private theorem le_foldr_max {l : List ℕ} {f : ℕ → ℕ} {a : ℕ} (ha : a ∈ l) :
    f a ≤ (l.map f).foldr max 0 := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp ha with rfl | ha
    · exact le_max_left _ _
    · exact (ih ha).trans (le_max_right _ _)

private theorem sum_le_card_mul {l : List ℕ} {f : ℕ → ℕ} {B : ℕ} (h : ∀ a ∈ l, f a ≤ B) :
    (l.map f).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have := h a (by simp); have := ih fun b hb => h b (by simp [hb]); omega

/-- Unfolding a well-formed gate computes its value at the requested polarity.

**Proof sketch.** Case on the gate kind and the polarity.  At positive polarity an
`∧` (`∨`) gate becomes an `∧` (`∨`) node of the positively unfolded arguments, which
evaluates correctly by hypothesis.  At negative polarity De Morgan applies: `¬(⋀ aᵢ)`
is the `∨` of the negated arguments and `¬(⋁ aᵢ)` the `∧` of them.  A `¬` gate has
exactly one argument (well-formedness) and unfolds to that argument at flipped
polarity. -/
theorem unfoldGate_eval (g : DAGGate) (hg : g.WellFormed) (t : ℕ → Bool → TreeCircuit n)
    (vals : List Bool) (x : Fin n → Bool)
    (ht : ∀ a ∈ g.args, ∀ p : Bool,
      (t a p).eval x = if p then vals.getD a false else !vals.getD a false)
    (pos : Bool) :
    (unfoldGate g t pos).eval x = if pos then g.eval vals else !g.eval vals := by
  rcases g with ⟨k, args⟩
  cases k
  · cases pos
    · simp only [unfoldGate, DAGGate.eval, Bool.false_eq_true, if_false,
        TreeCircuit.eval_node_false, List.any_map, Function.comp_def]
      rw [Bool.eq_iff_iff]
      simp only [List.any_eq_true, Bool.not_eq_true', List.all_eq_false]
      exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, by rw [ht a ha] at h; simpa using h⟩,
        fun ⟨a, ha, h⟩ => ⟨a, ha, by rw [ht a ha]; simpa using h⟩⟩
    · simp only [unfoldGate, DAGGate.eval, if_true, TreeCircuit.eval_node_true, List.all_map,
        Function.comp_def]
      rw [Bool.eq_iff_iff]
      simp only [List.all_eq_true]
      exact forall₂_congr fun a ha => by rw [ht a ha]; simp
  · cases pos
    · simp only [unfoldGate, DAGGate.eval, Bool.false_eq_true, if_false, Bool.not_false,
        TreeCircuit.eval_node_true, List.all_map, Function.comp_def]
      rw [Bool.eq_iff_iff]
      simp only [List.all_eq_true, Bool.not_eq_true', List.any_eq_false]
      exact forall₂_congr fun a ha => by rw [ht a ha]; simp
    · simp only [unfoldGate, DAGGate.eval, if_true, Bool.not_true,
        TreeCircuit.eval_node_false, List.any_map, Function.comp_def]
      rw [Bool.eq_iff_iff]
      simp only [List.any_eq_true]
      exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, by rw [ht a ha] at h; simpa using h⟩,
        fun ⟨a, ha, h⟩ => ⟨a, ha, by rw [ht a ha]; simpa using h⟩⟩
  · obtain ⟨a, rfl⟩ : ∃ a, args = [a] := List.length_eq_one_iff.mp (hg.2 rfl)
    simp only [unfoldGate, DAGGate.eval, List.headD_cons, List.all_cons, List.all_nil,
      Bool.and_true]
    rw [ht a (by simp)]
    cases pos <;> simp

/-- Unfolding a well-formed gate adds one level for `∧`/`∨` and none for `¬`. -/
theorem unfoldGate_depth_le (g : DAGGate) (hg : g.WellFormed) (t : ℕ → Bool → TreeCircuit n)
    (B : ℕ) (ht : ∀ a ∈ g.args, ∀ p : Bool, (t a p).depth ≤ B) (pos : Bool) :
    (unfoldGate g t pos).depth ≤ B + 1 := by
  rcases g with ⟨k, args⟩
  have hnode : ∀ b p, (TreeCircuit.node b (args.map fun a => t a p)).depth ≤ B + 1 := by
    intro b p
    rw [TreeCircuit.depth_node, maxDepth_map]
    have := foldr_max_le (l := args) (f := fun a => (t a p).depth) fun a ha => ht a ha p
    omega
  cases k
  · exact hnode _ _
  · exact hnode _ _
  · obtain ⟨a, rfl⟩ : ∃ a, args = [a] := List.length_eq_one_iff.mp (hg.2 rfl)
    exact (ht a (by simp) _).trans (Nat.le_succ _)

/-- Unfolding a well-formed gate with at most `k` arguments, whose argument trees all have
fan-in at most `k`, gives a tree of fan-in at most `k`. -/
theorem unfoldGate_maxFanin_le (g : DAGGate) (hg : g.WellFormed) (t : ℕ → Bool → TreeCircuit n)
    {k : ℕ} (hlen : g.args.length ≤ k) (ht : ∀ a ∈ g.args, ∀ p : Bool, (t a p).maxFanin ≤ k)
    (pos : Bool) : (unfoldGate g t pos).maxFanin ≤ k := by
  rcases g with ⟨kd, args⟩
  have hnode : ∀ b p, (TreeCircuit.node b (args.map fun a => t a p)).maxFanin ≤ k := by
    intro b p
    rw [TreeCircuit.maxFanin_node, maxFaninL_map, List.length_map]
    exact max_le hlen (foldr_max_le fun a ha => ht a ha p)
  cases kd
  · exact hnode _ _
  · exact hnode _ _
  · obtain ⟨a, rfl⟩ : ∃ a, args = [a] := List.length_eq_one_iff.mp (hg.2 rfl)
    exact ht a (by simp) _

/-- Size bound for unfolding a gate: if a well-formed gate has at most `k` arguments and
every argument tree (at either polarity) has size at most `B`, the unfolded tree has size
at most `1 + k * B`. -/
theorem unfoldGate_size_le (g : DAGGate) (hg : g.WellFormed) (t : ℕ → Bool → TreeCircuit n)
    {k B : ℕ} (hlen : g.args.length ≤ k) (ht : ∀ a ∈ g.args, ∀ p : Bool, (t a p).size ≤ B) :
    ∀ pos, (unfoldGate g t pos).size ≤ 1 + k * B := by
  intro pos
  rcases g with ⟨kd, args⟩
  have hnode : ∀ b p, (TreeCircuit.node b (args.map fun a => t a p)).size ≤ 1 + k * B := by
    intro b p
    rw [TreeCircuit.size_node, sumSize_map]
    have := sum_le_card_mul (l := args) (f := fun a => (t a p).size) fun a ha => ht a ha p
    have : args.length * B ≤ k * B := Nat.mul_le_mul_right _ hlen
    omega
  cases kd
  · exact hnode _ _
  · exact hnode _ _
  · obtain ⟨a, rfl⟩ : ∃ a, args = [a] := List.length_eq_one_iff.mp (hg.2 rfl)
    have := ht a (by simp) (!pos)
    have hk : 1 ≤ k := by simpa using hlen
    simp only [unfoldGate, List.headD_cons]
    nlinarith

namespace DAGCircuit

variable (C : DAGCircuit n)

private theorem getD_gates {i : ℕ} (hi : i < C.gates.length) :
    C.gates.getD i (constGate true) = C.gates[i] := List.getD_eq_getElem _ _ hi

/-- The args of the gate at vertex `v ≥ n`. -/
private theorem args_lt_vertex {v : ℕ} (hn : ¬ v < n) (hv : v < n + C.gates.length) :
    ∀ a ∈ (C.gates[v - n]'(by omega)).args, a < v := by
  intro a ha
  have := C.args_lt (v - n) (by omega) a ha
  omega

/-- A gate vertex is deeper than every vertex it reads. -/
private theorem depthAt_lt_of_arg {v : ℕ} (hn : ¬ v < n) (hv : v < n + C.gates.length)
    {a : ℕ} (ha : a ∈ (C.gates[v - n]'(by omega)).args) : C.depthAt a < C.depthAt v := by
  have hd := C.depthAt_gate (i := v - n) (by omega)
  rw [show n + (v - n) = v by omega] at hd
  rw [hd, DAGGate.depth]
  have := le_foldr_max (f := fun a => C.depths.getD a 0) ha
  simp only [depthAt] at this ⊢
  omega

/-- Correctness of unfolding a vertex: for a well-formed DAG and enough fuel (`v < fuel`),
the tree obtained by unfolding vertex `v` at polarity `pos` evaluates to the vertex's
value when `pos = true` and to its negation when `pos = false`. -/
theorem unfoldVertex_eval (hwf : C.IsWellFormed) (x : Fin n → Bool) :
    ∀ (fuel v : ℕ) (pos : Bool), v < n + C.gates.length → v < fuel →
      (unfoldVertex n C.gates fuel v pos).eval x =
        if pos then (C.values x).getD v false else !(C.values x).getD v false
  | 0, v, _, _, hf => absurd hf (Nat.not_lt_zero v)
  | fuel + 1, v, pos, hv, hf => by
    by_cases hn : v < n
    · have hval := C.values_getD_input x ⟨v, hn⟩
      simp only at hval
      simp only [unfoldVertex, hn, dite_true, TreeCircuit.eval, Lit.eval, hval]
    · have hi : v - n < C.gates.length := by omega
      have hval := C.values_getD_gate x hi
      rw [show n + (v - n) = v by omega] at hval
      have hargs := C.args_lt_vertex hn hv
      simp only [unfoldVertex, hn, dite_false, C.getD_gates hi]
      rw [hval]
      exact unfoldGate_eval _ (hwf _ (List.getElem_mem hi)) _ _ x
        (fun a ha p => unfoldVertex_eval hwf x fuel a p (by have := hargs a ha; omega)
          (by have := hargs a ha; omega)) pos

/-- The tree circuit obtained by unfolding a well-formed DAG circuit computes the same
Boolean function: `C.toTree.eval x = C.eval x` for every input `x`. -/
theorem toTree_eval (hwf : C.IsWellFormed) (x : Fin n → Bool) :
    C.toTree.eval x = C.eval x := by
  rw [toTree, C.unfoldVertex_eval hwf x _ _ true C.output_lt (Nat.lt_succ_self _)]
  rfl

/-- Unfolding vertex `v` of a well-formed DAG (with enough fuel, at either polarity)
gives a tree of depth at most the depth of `v` in the DAG. -/
theorem unfoldVertex_depth_le (hwf : C.IsWellFormed) :
    ∀ (fuel v : ℕ) (pos : Bool), v < n + C.gates.length → v < fuel →
      (unfoldVertex n C.gates fuel v pos).depth ≤ C.depthAt v
  | 0, v, _, _, hf => absurd hf (Nat.not_lt_zero v)
  | fuel + 1, v, pos, hv, hf => by
    by_cases hn : v < n
    · simp [unfoldVertex, hn, TreeCircuit.depth]
    · have hi : v - n < C.gates.length := by omega
      have hargs := C.args_lt_vertex hn hv
      have hd := C.depthAt_gate hi
      rw [show n + (v - n) = v by omega] at hd
      simp only [unfoldVertex, hn, dite_false, C.getD_gates hi]
      have hB : ∀ a ∈ (C.gates[v - n]).args, ∀ p : Bool,
          (unfoldVertex n C.gates fuel a p).depth ≤ C.depthAt v - 1 := fun a ha p =>
        (unfoldVertex_depth_le hwf fuel a p (by have := hargs a ha; omega)
          (by have := hargs a ha; omega)).trans
          (by have := C.depthAt_lt_of_arg hn hv ha; omega)
      have := unfoldGate_depth_le _ (hwf _ (List.getElem_mem hi)) _ _ hB pos
      have hpos : 1 ≤ C.depthAt v := by rw [hd, DAGGate.depth]; omega
      omega

/-- Unfolding does not increase depth: `¬` gates disappear. -/
theorem toTree_depth_le (hwf : C.IsWellFormed) : C.toTree.depth ≤ C.depth :=
  C.unfoldVertex_depth_le hwf _ _ _ C.output_lt (Nat.lt_succ_self _)

/-- Unfolding any vertex of a well-formed DAG whose gates all read at most `k` vertices
gives a tree of fan-in at most `k` (for any fuel and polarity). -/
theorem unfoldVertex_maxFanin_le (hwf : C.IsWellFormed) {k : ℕ}
    (hk : ∀ g ∈ C.gates, g.args.length ≤ k) :
    ∀ (fuel v : ℕ) (pos : Bool), v < n + C.gates.length →
      (unfoldVertex n C.gates fuel v pos).maxFanin ≤ k
  | 0, v, _, _ => by simp [unfoldVertex, TreeCircuit.maxFanin]
  | fuel + 1, v, pos, hv => by
    by_cases hn : v < n
    · simp [unfoldVertex, hn, TreeCircuit.maxFanin]
    · have hi : v - n < C.gates.length := by omega
      have hargs := C.args_lt_vertex hn hv
      simp only [unfoldVertex, hn, dite_false, C.getD_gates hi]
      exact unfoldGate_maxFanin_le _ (hwf _ (List.getElem_mem hi)) _
        (hk _ (List.getElem_mem hi))
        (fun a ha p => unfoldVertex_maxFanin_le hwf hk fuel a p
          (by have := hargs a ha; omega)) pos

/-- Unfolding keeps the fan-in bound. -/
theorem toTree_maxFanin_le (hwf : C.IsWellFormed) {k : ℕ}
    (hk : ∀ g ∈ C.gates, g.args.length ≤ k) : C.toTree.maxFanin ≤ k :=
  C.unfoldVertex_maxFanin_le hwf hk _ _ _ C.output_lt

/-- Size bound for unfolding a vertex: in a well-formed DAG whose gates read at most `k`
vertices, unfolding vertex `v` (with enough fuel, at either polarity) gives a tree with
at most `(k + 1) ^ d` nodes, where `d` is the depth of `v`.

**Proof sketch.** Induction on the fuel.  An input vertex unfolds to a single literal,
of size `1 ≤ (k + 1) ^ d`.  A gate vertex has depth `d ≥ 1`, and each vertex it reads is
strictly shallower, so by induction each argument tree has size at most
`(k + 1) ^ (d - 1)`.  Unfolding the gate gives size at most `1 + k (k + 1) ^ (d - 1)`,
which is at most `(k + 1) (k + 1) ^ (d - 1) = (k + 1) ^ d`. -/
theorem unfoldVertex_size_le (hwf : C.IsWellFormed) {k : ℕ}
    (hk : ∀ g ∈ C.gates, g.args.length ≤ k) :
    ∀ (fuel v : ℕ) (pos : Bool), v < n + C.gates.length → v < fuel →
      (unfoldVertex n C.gates fuel v pos).size ≤ (k + 1) ^ C.depthAt v
  | 0, v, _, _, hf => absurd hf (Nat.not_lt_zero v)
  | fuel + 1, v, pos, hv, hf => by
    by_cases hn : v < n
    · simp [unfoldVertex, hn, TreeCircuit.size]
      exact Nat.one_le_pow _ _ (by omega)
    · have hi : v - n < C.gates.length := by omega
      have hargs := C.args_lt_vertex hn hv
      have hd := C.depthAt_gate hi
      rw [show n + (v - n) = v by omega] at hd
      have hpos : 1 ≤ C.depthAt v := by rw [hd, DAGGate.depth]; omega
      simp only [unfoldVertex, hn, dite_false, C.getD_gates hi]
      have hB : ∀ a ∈ (C.gates[v - n]).args, ∀ p : Bool,
          (unfoldVertex n C.gates fuel a p).size ≤ (k + 1) ^ (C.depthAt v - 1) :=
        fun a ha p =>
          (unfoldVertex_size_le hwf hk fuel a p (by have := hargs a ha; omega)
            (by have := hargs a ha; omega)).trans
            (Nat.pow_le_pow_right (by omega)
              (by have := C.depthAt_lt_of_arg hn hv ha; omega))
      have := unfoldGate_size_le _ (hwf _ (List.getElem_mem hi)) _
        (hk _ (List.getElem_mem hi)) hB pos
      have hpow : (k + 1) ^ C.depthAt v = (k + 1) * (k + 1) ^ (C.depthAt v - 1) := by
        rw [← pow_succ']; congr 1; omega
      have h1 : 1 ≤ (k + 1) ^ (C.depthAt v - 1) := Nat.one_le_pow _ _ (by omega)
      rw [hpow]
      nlinarith

/-- The unfolded tree has at most `(k + 1) ^ depth` nodes when every gate reads at most `k`
vertices — exponential in depth, as duplication of shared vertices must be. -/
theorem toTree_size_le (hwf : C.IsWellFormed) {k : ℕ} (hk : ∀ g ∈ C.gates, g.args.length ≤ k) :
    C.toTree.size ≤ (k + 1) ^ C.depth :=
  C.unfoldVertex_size_le hwf hk _ _ _ C.output_lt (Nat.lt_succ_self _)

end DAGCircuit

end BoolCircuit
