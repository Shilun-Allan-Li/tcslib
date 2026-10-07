/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import TCSlib.Complexity.CircuitComplexity.TreeDAG
import TCSlib.Complexity.CircuitComplexity.FanOut

/-!
# Formulas are the circuits of fan-out one

[AB09, p. 108]: "the Boolean formulas studied in earlier chapters are circuits where the
fan-out (i.e., number of outgoing edges) of each vertex is 1."  The library's formula model
is `BoolCircuit.TreeCircuit` (`∧`/`∨` nodes over literals, negation pushed to the inputs).
We prove both directions, over the book's circuit model `BoolCircuit.DAGCircuit`
([AB09, Def 6.1]) and its fan-out `BoolCircuit.DAGCircuit.fanout` (`FanOut.lean`).

* **Formula → fan-out-one circuit.**  The linear compilation `TreeCircuit.toDAG`
  (`TreeDAG.lean`) produces a circuit in which every gate vertex has fan-out at most one;
  more precisely, the output gate is read by no gate and every other gate by exactly one.
* **Fan-out-one circuit → formula.**  A fan-in-two circuit whose gates all have fan-out at
  most one unfolds (`DAGCircuit.toTree`) into a formula of the same function with at most
  `3 · #gates + 1 ≤ 4 · |C|` nodes.  The unfolding is exponential in general
  (`DAGCircuit.toTree_size_le`); fan-out one is exactly what makes it linear, since no gate
  is ever copied.

## Main definitions

* `BoolCircuit.CompileFanout`, `BoolCircuit.CompileListFanout` — the fan-out invariants of
  the formula compilation.
* `BoolCircuit.DAGCircuit.unfoldSize`, `BoolCircuit.DAGCircuit.rootSet` — the size of a
  vertex's unfolding and the unread gate vertices of a prefix, for the linear bound.

## Main results

* `BoolCircuit.TreeCircuit.toDAG_fanout_le_one`, `toDAG_fanout_eq_one`,
  `toDAG_fanout_output` — the gates of a compiled formula have fan-out one (zero at the
  output).
* `BoolCircuit.TreeCircuit.exists_toDAG_input_fanout_two` — an input vertex may be read
  twice.
* `BoolCircuit.TreeCircuit.exists_dagCircuit_fanout_le_one` — a fan-in-two formula of size
  `s` is a fan-in-two circuit of size at most `n + s` with gate fan-out at most one.
* `BoolCircuit.DAGCircuit.toTree_size_le_of_fanout_le_one` — the linear unfolding bound.
* `BoolCircuit.DAGCircuit.exists_treeCircuit_of_fanout_le_one` — the converse headline.

## Divergences from [AB09, p. 108]

* **Inputs.**  "The fan-out of each vertex is 1" cannot hold of the *input* vertices: in
  [AB09, Def 6.1] each variable is a single source, while a formula may read a variable
  several times (`(x ∧ y) ∨ (¬x ∧ ¬y)`).  The statement is true of every *gate* vertex, and
  that is what we prove; `exists_toDAG_input_fanout_two` shows the input restriction cannot
  be added.  The output gate has fan-out `0` (being the output is not an edge).
* **Negations.**  The earlier chapters' formulas allow `¬` anywhere; `TreeCircuit` keeps it
  at the literals.  The unfolding pushes each `¬` gate down by De Morgan, which flips node
  labels but copies nothing, so no size is lost; conversely a negative literal compiles to
  one `¬` gate.  De Morgan normalisation to negation normal form therefore does not
  increase the node count: a vertex unfolds to trees of the same size at either polarity
  (`size_unfoldVertex_polarity`, from `size_unfoldGate_polarity`), and a `¬` gate
  contributes no node (`size_unfoldGate_le`).
* **Explicit constants.**  The book's claim is an identification; we give the sizes: `n + s`
  one way and `3 · #gates + 1` the other (a gate contributes its own node plus at most two
  literal leaves).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, p. 108.)
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

variable {n : ℕ}

/-! ## Formula → fan-out-one circuit -/

/-- The fan-out bookkeeping of compiling one formula after the gates `gs`, which appends
`ext` and returns the vertex `r`: the new gates read no old gate vertex, read every gate
vertex at most once, never read `r`, and read every new gate vertex other than `r` exactly
once; `r` is an input or a new vertex. -/
structure CompileFanout (n : ℕ) (gs ext : List DAGGate) (r : ℕ) : Prop where
  old_unread : ∀ v, n ≤ v → v < n + gs.length → fanoutIn ext v = 0
  le_one : ∀ v, n ≤ v → fanoutIn ext v ≤ 1
  root_unread : n ≤ r → fanoutIn ext r = 0
  root_new : r < n ∨ n + gs.length ≤ r
  eq_one : ∀ v, n + gs.length ≤ v → v < n + gs.length + ext.length → v ≠ r →
    fanoutIn ext v = 1

/-- The fan-out bookkeeping of compiling a list of formulas, returning the vertices `rs`. -/
structure CompileListFanout (n : ℕ) (gs ext : List DAGGate) (rs : List ℕ) : Prop where
  old_unread : ∀ v, n ≤ v → v < n + gs.length → fanoutIn ext v = 0
  le_one : ∀ v, n ≤ v → fanoutIn ext v ≤ 1
  roots_unread : ∀ r ∈ rs, n ≤ r → fanoutIn ext r = 0
  roots_new : ∀ r ∈ rs, r < n ∨ n + gs.length ≤ r
  eq_one : ∀ v, n + gs.length ≤ v → v < n + gs.length + ext.length → v ∉ rs →
    fanoutIn ext v = 1

/-- Gates appended to an acyclic list read no vertex created after them. -/
private theorem fanoutIn_ext_eq_zero {gs ext : List DAGGate} (h : GatesAcyclic n (gs ++ ext))
    {v : ℕ} (hv : n + (gs ++ ext).length ≤ v) : fanoutIn ext v = 0 := by
  have := fanoutIn_eq_zero_of_le h hv
  rw [fanoutIn_append] at this
  omega

/-- Fan-out bookkeeping for compiling a list of formulas, given it for each member.

**Proof sketch.** Induction on the list.  Compile `c` (appending `e₁`, returning `r₁`) and
then the rest (appending `e₂`, returning `rs`).  Vertices created before `e₂` are not read
by `e₂` (the rest's `old_unread`), and vertices created after `e₁` are not read by `e₁`
(acyclicity); so every gate vertex's fan-out in `e₁ ++ e₂` is its fan-out in one of the
two parts, and each clause follows from the corresponding clause for that part. -/
theorem compileTrees_fanout :
    ∀ (cs : List (TreeCircuit n)),
      (∀ c ∈ cs, ∀ gs, GatesAcyclic n gs → ∃ ext, (compileTree n c gs).1 = gs ++ ext ∧
        CompileFanout n gs ext (compileTree n c gs).2) →
      ∀ gs, GatesAcyclic n gs → ∃ ext, (compileTrees n cs gs).1 = gs ++ ext ∧
        CompileListFanout n gs ext (compileTrees n cs gs).2
  | [], _, gs, _ => by
    refine ⟨[], by simp [compileTrees], ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;> simp [compileTrees, fanoutIn]
  | c :: cs, ih, gs, hgs => by
    obtain ⟨e1, he1, f1⟩ := ih c (by simp) gs hgs
    have hs1 := compileTree_spec c gs hgs
    set r1 := compileTree n c gs with hr1
    obtain ⟨e2, he2, f2⟩ := compileTrees_fanout cs (fun c' hc' => ih c' (by simp [hc'])) r1.1
      hs1.acyclic
    have hs2 := compileTrees_spec cs (fun c' _ => compileTree_spec c') r1.1 hs1.acyclic
    set r2 := compileTrees n cs r1.1 with hr2
    have hres : compileTrees n (c :: cs) gs = (r2.1, r1.2 :: r2.2) := by
      simp [compileTrees, hr1, hr2]
    rw [hres]
    refine ⟨e1 ++ e2, by rw [he2, he1, List.append_assoc], ?_⟩
    have hl1 : r1.1.length = gs.length + e1.length := by rw [he1]; simp
    have e1_zero : ∀ v, n + r1.1.length ≤ v → fanoutIn e1 v = 0 := fun v hv =>
      fanoutIn_ext_eq_zero (gs := gs) (by rw [← he1]; exact hs1.acyclic) (by rw [← he1]; exact hv)
    refine ⟨fun v hv1 hv2 => ?_, fun v hv => ?_, fun r hr hrn => ?_, fun r hr => ?_,
      fun v hv1 hv2 hvr => ?_⟩
    · rw [fanoutIn_append, f1.old_unread v hv1 hv2, f2.old_unread v hv1 (by omega)]
    · rw [fanoutIn_append]
      by_cases h : v < n + r1.1.length
      · rw [f2.old_unread v hv h]; have := f1.le_one v hv; omega
      · rw [e1_zero v (by omega)]; have := f2.le_one v hv; omega
    · rw [fanoutIn_append]
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [f1.root_unread hrn, f2.old_unread _ hrn hs1.vertex_lt]
      · rw [f2.roots_unread r hr hrn]
        rcases f2.roots_new r hr with h | h
        · omega
        · rw [e1_zero r h]
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact f1.root_new
      · rcases f2.roots_new r hr with h | h
        · exact Or.inl h
        · right; omega
    · simp only [List.mem_cons, not_or] at hvr
      simp only [List.length_append] at hv2
      rw [fanoutIn_append]
      by_cases h : v < n + r1.1.length
      · rw [f1.eq_one v hv1 (by omega) hvr.1, f2.old_unread v (by omega) h]
      · rw [e1_zero v (by omega), f2.eq_one v (by omega) (by omega) hvr.2]

/-- Fan-out bookkeeping for compiling one formula.

**Proof sketch.** Structural induction.  A positive literal appends nothing.  A negative
literal appends one `¬` gate reading an input, so no gate vertex is read, and the new gate
is the returned vertex.  A node compiles its children (`compileTrees_fanout`) and appends
one gate `g` reading the children's vertices: a child's gate vertex was unread, so it is
now read exactly once, by `g`; every other vertex keeps its fan-out; `g` is the returned
vertex and nothing reads it. -/
theorem compileTree_fanout (c : TreeCircuit n) :
    ∀ gs, GatesAcyclic n gs → ∃ ext, (compileTree n c gs).1 = gs ++ ext ∧
      CompileFanout n gs ext (compileTree n c gs).2 := by
  induction c using TreeCircuit.ind with
  | hlit l =>
    intro gs hgs
    rcases l with ⟨i, s⟩
    cases s
    · have hres : compileTree n (.lit ⟨i, false⟩) gs =
          (gs ++ [⟨.not, [i]⟩], n + gs.length) := by
        simp [compileTree]
      rw [hres]
      have hz : ∀ v, n ≤ v → fanoutIn [⟨.not, [(i : ℕ)]⟩] v = 0 := by
        intro v hv
        rw [fanoutIn_singleton, if_neg]
        simp only [List.mem_singleton]
        have := i.isLt
        omega
      refine ⟨_, rfl, fun v hv _ => hz v hv, fun v hv => by rw [hz v hv]; omega,
        fun hr => hz _ hr, Or.inr le_rfl, fun v hv1 hv2 hvr => ?_⟩
      simp only [List.length_singleton] at hv2
      omega
    · have hres : compileTree n (.lit ⟨i, true⟩) gs = (gs, (i : ℕ)) := by simp [compileTree]
      rw [hres]
      refine ⟨[], by simp, fun v _ _ => by simp [fanoutIn], fun v _ => by simp [fanoutIn],
        fun _ => by simp [fanoutIn], Or.inl i.isLt, fun v hv1 hv2 _ => ?_⟩
      simp only [List.length_nil] at hv2
      omega
  | hnode b cs ih =>
    intro gs hgs
    obtain ⟨e, he, f⟩ := compileTrees_fanout cs ih gs hgs
    have h := compileTrees_spec cs (fun c' _ => compileTree_spec c') gs hgs
    set r := compileTrees n cs gs with hr
    set g : DAGGate := ⟨nodeKind b, r.2.dedup⟩ with hg
    have hres : compileTree n (.node b cs) gs = (r.1 ++ [g], n + r.1.length) := by
      rw [compileTree]
    rw [hres]
    refine ⟨e ++ [g], by rw [he, List.append_assoc], ?_⟩
    have hlen : r.1.length = gs.length + e.length := by rw [he]; simp
    have hg_fan : ∀ v, fanoutIn [g] v = if v ∈ r.2 then 1 else 0 := by
      intro v
      rw [fanoutIn_singleton]
      simp [hg, List.mem_dedup]
    have he_zero : ∀ v, n + r.1.length ≤ v → fanoutIn e v = 0 := fun v hv =>
      fanoutIn_ext_eq_zero (gs := gs) (by rw [← he]; exact h.acyclic) (by rw [← he]; exact hv)
    refine ⟨fun v hv1 hv2 => ?_, fun v hv => ?_, fun _ => ?_, Or.inr (by omega),
      fun v hv1 hv2 hvr => ?_⟩
    · rw [fanoutIn_append, f.old_unread v hv1 hv2, hg_fan]
      have : v ∉ r.2 := fun hm => by rcases f.roots_new v hm with h' | h' <;> omega
      simp [this]
    · rw [fanoutIn_append, hg_fan]
      split_ifs with hm
      · rw [f.roots_unread v hm hv]
      · have := f.le_one v hv; omega
    · rw [fanoutIn_append, he_zero _ le_rfl, hg_fan]
      have : n + r.1.length ∉ r.2 := fun hm => by have := h.vertex_lt _ hm; omega
      simp [this]
    · simp only [List.length_append, List.length_singleton] at hv2
      rw [fanoutIn_append, hg_fan]
      split_ifs with hm
      · rw [f.roots_unread v hm (by omega)]
      · rw [f.eq_one v hv1 (by omega) hm]

namespace TreeCircuit

/-- The fan-out bookkeeping of the whole compilation `c.toDAG`. -/
private theorem toDAG_fanoutSpec (c : TreeCircuit n) :
    CompileFanout n [] c.toDAG.gates c.toDAG.output := by
  obtain ⟨ext, he, f⟩ := compileTree_fanout c [] GatesAcyclic.nil
  simp only [List.nil_append] at he
  have hg : c.toDAG.gates = ext := he
  rw [hg]
  exact f

/-- **Formulas are fan-out-one circuits.**  In the circuit compiled from a formula, every
gate vertex has fan-out at most one.  [AB09, p. 108]

Input vertices are excluded: a formula may read a variable several times, and in the
book's model each variable is one source (`exists_toDAG_input_fanout_two`). -/
theorem toDAG_fanout_le_one (c : TreeCircuit n) {v : ℕ} (hv : n ≤ v) :
    c.toDAG.fanout v ≤ 1 :=
  c.toDAG_fanoutSpec.le_one v hv

/-- The output of a compiled formula, if it is a gate, is read by no gate. -/
theorem toDAG_fanout_output (c : TreeCircuit n) (h : n ≤ c.toDAG.output) :
    c.toDAG.fanout c.toDAG.output = 0 :=
  c.toDAG_fanoutSpec.root_unread h

/-- In the circuit compiled from a formula, every gate vertex other than the output has
fan-out exactly one.  [AB09, p. 108] -/
theorem toDAG_fanout_eq_one (c : TreeCircuit n) {v : ℕ} (hv : n ≤ v) (hvs : v < c.toDAG.size)
    (hvo : v ≠ c.toDAG.output) : c.toDAG.fanout v = 1 :=
  c.toDAG_fanoutSpec.eq_one v (by simpa using hv) (by simpa [DAGCircuit.size] using hvs) hvo

/-- The fan-out restriction cannot be extended to the inputs: the formula `x₀ ∧ ¬x₀`
compiles to a circuit whose input vertex `x₀` is read by two gates. -/
theorem exists_toDAG_input_fanout_two : ∃ c : TreeCircuit 1, c.toDAG.fanout 0 = 2 :=
  ⟨.node true [.lit ⟨0, true⟩, .lit ⟨0, false⟩], by
    simp [toDAG, DAGCircuit.fanout, fanoutIn, compileTree, compileTrees, nodeKind]⟩

/-- A fan-in-two formula with `s` nodes is computed by a fan-in-two circuit of size at most
`n + s` whose gates all have fan-out at most one.  [AB09, p. 108] -/
theorem exists_dagCircuit_fanout_le_one (c : TreeCircuit n) (hc : c.maxFanin ≤ 2) :
    ∃ C : DAGCircuit n, C.IsFaninTwo ∧ (∀ v, n ≤ v → C.fanout v ≤ 1) ∧
      (∀ x, C.eval x = c.eval x) ∧ C.size ≤ n + c.size :=
  ⟨c.toDAG, c.toDAG_isFaninTwo hc, fun _ hv => c.toDAG_fanout_le_one hv, c.toDAG_eval,
    c.toDAG_size_le⟩

end TreeCircuit

/-! ## Fan-out-one circuit → formula -/

/-- Unfolding a well-formed gate depends only on how its inputs unfold. -/
theorem unfoldGate_congr {g : DAGGate} (hg : g.WellFormed) {t t' : ℕ → Bool → TreeCircuit n}
    (h : ∀ a ∈ g.args, ∀ p, t a p = t' a p) (p : Bool) :
    unfoldGate g t p = unfoldGate g t' p := by
  rcases g with ⟨k, args⟩
  cases k
  · simp only [unfoldGate]
    rw [List.map_congr_left fun a ha => h a ha p]
  · simp only [unfoldGate]
    rw [List.map_congr_left fun a ha => h a ha p]
  · obtain ⟨a, rfl⟩ : ∃ a, args = [a] := List.length_eq_one_iff.mp (hg.2 rfl)
    simp only [unfoldGate, List.headD_cons]
    exact h a (by simp) _

/-- Unfolding a gate at either polarity gives trees of the same size, provided its inputs
do: De Morgan swaps labels, never shapes. -/
theorem size_unfoldGate_polarity (g : DAGGate) (t : ℕ → Bool → TreeCircuit n)
    (ht : ∀ a p q, (t a p).size = (t a q).size) (p q : Bool) :
    (unfoldGate g t p).size = (unfoldGate g t q).size := by
  rcases g with ⟨k, args⟩
  cases k
  · simp only [unfoldGate, TreeCircuit.size_node, sumSize_map]
    rw [List.map_congr_left fun a _ => ht a p q]
  · simp only [unfoldGate, TreeCircuit.size_node, sumSize_map]
    rw [List.map_congr_left fun a _ => ht a p q]
  · exact ht _ _ _

/-- Unfolding a well-formed gate gives a tree of size at most one plus the sizes of its
inputs' trees (the `¬` gate adds nothing). -/
theorem size_unfoldGate_le (g : DAGGate) (hg : g.WellFormed) (t : ℕ → Bool → TreeCircuit n)
    (ht : ∀ a p q, (t a p).size = (t a q).size) (p : Bool) :
    (unfoldGate g t p).size ≤ 1 + (g.args.map fun a => (t a p).size).sum := by
  rcases g with ⟨k, args⟩
  cases k
  · simp [unfoldGate, TreeCircuit.size_node, sumSize_map]
  · simp [unfoldGate, TreeCircuit.size_node, sumSize_map]
  · obtain ⟨a, rfl⟩ : ∃ a, args = [a] := List.length_eq_one_iff.mp (hg.2 rfl)
    simp only [unfoldGate, List.headD_cons, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, ht a (!p) p]
    omega

/-- The size of an unfolded vertex does not depend on the polarity. -/
theorem size_unfoldVertex_polarity (gs : List DAGGate) :
    ∀ (fuel v : ℕ) (p q : Bool),
      (unfoldVertex n gs fuel v p).size = (unfoldVertex n gs fuel v q).size
  | 0, _, _, _ => rfl
  | fuel + 1, v, p, q => by
    by_cases hn : v < n
    · simp [unfoldVertex, hn, TreeCircuit.size]
    · simp only [unfoldVertex, hn, dite_false]
      exact size_unfoldGate_polarity _ _ (size_unfoldVertex_polarity gs fuel) p q

namespace DAGCircuit

variable (C : DAGCircuit n)

/-- With enough fuel, unfolding a vertex of a well-formed circuit does not depend on the
fuel. -/
theorem unfoldVertex_fuel_congr (hwf : C.IsWellFormed) :
    ∀ (f f' v : ℕ) (p : Bool), v < f → v < f' →
      unfoldVertex n C.gates f v p = unfoldVertex n C.gates f' v p
  | 0, _, v, _, h, _ => absurd h (Nat.not_lt_zero v)
  | _ + 1, 0, v, _, _, h => absurd h (Nat.not_lt_zero v)
  | f + 1, f' + 1, v, p, h, h' => by
    by_cases hn : v < n
    · simp [unfoldVertex, hn]
    · simp only [unfoldVertex, hn, dite_false]
      by_cases hi : v - n < C.gates.length
      · rw [List.getD_eq_getElem _ _ hi]
        refine unfoldGate_congr (hwf _ (List.getElem_mem hi)) (fun a ha q => ?_) p
        have := C.args_lt (v - n) hi a ha
        exact unfoldVertex_fuel_congr hwf f f' a q (by omega) (by omega)
      · rw [List.getD_eq_default _ _ (by omega)]
        simp [unfoldGate, constGate]

/-- The size of the formula unfolding vertex `v` (positively, with just enough fuel). -/
def unfoldSize (v : ℕ) : ℕ := (unfoldVertex n C.gates (v + 1) v true).size

/-- An input vertex unfolds to a single literal. -/
theorem unfoldSize_input {v : ℕ} (hv : v < n) : C.unfoldSize v = 1 := by
  simp [unfoldSize, unfoldVertex, hv, TreeCircuit.size]

/-- The unfolding of gate vertex `n + k` has at most `3` nodes besides the unfoldings of the
gate vertices it reads.

**Proof sketch.** The gate unfolds to one node over its inputs' unfoldings (or, for `¬`,
to its input's unfolding at the other polarity, of the same size).  By fuel independence
each input `a` contributes `C.unfoldSize a`; an input vertex contributes `1`, and there
are at most two inputs. -/
theorem unfoldSize_gate_le (hC : C.IsFaninTwo) {k : ℕ} (hk : k < C.gates.length) :
    C.unfoldSize (n + k) ≤
      3 + ∑ a ∈ (C.gates[k]).args.toFinset.filter (n ≤ ·), C.unfoldSize a := by
  classical
  set g := C.gates[k] with hg
  have hwf : g.WellFormed := hC.1 g (List.getElem_mem hk)
  have hlen : g.args.length ≤ 2 := hC.2 g (List.getElem_mem hk)
  have hargs : ∀ a ∈ g.args, a < n + k := fun a ha => C.args_lt k hk a ha
  have hunf : unfoldVertex n C.gates (n + k + 1) (n + k) true =
      unfoldGate g (unfoldVertex n C.gates (n + k)) true := by
    simp only [unfoldVertex, show ¬ n + k < n by omega, dite_false,
      show n + k - n = k by omega, List.getD_eq_getElem _ _ hk, hg]
  have hle := size_unfoldGate_le g hwf (unfoldVertex n C.gates (n + k))
    (size_unfoldVertex_polarity C.gates (n + k)) true
  have hterm : ∀ a ∈ g.args,
      (unfoldVertex n C.gates (n + k) a true).size = C.unfoldSize a := fun a ha => by
    rw [unfoldSize, C.unfoldVertex_fuel_congr hC.1 (n + k) (a + 1) a true (hargs a ha)
      (by omega)]
  rw [unfoldSize, hunf]
  refine hle.trans ?_
  rw [List.map_congr_left hterm, ← List.sum_toFinset _ hwf.1,
    ← Finset.sum_filter_add_sum_filter_not g.args.toFinset (n ≤ ·)]
  have hin : ∑ a ∈ g.args.toFinset.filter (fun a => ¬ n ≤ a), C.unfoldSize a ≤ 2 := by
    rw [Finset.sum_congr rfl fun a ha => C.unfoldSize_input
      (by simp only [Finset.mem_filter] at ha; omega)]
    rw [← Finset.card_eq_sum_ones]
    calc _ ≤ g.args.toFinset.card := Finset.card_filter_le _ _
      _ = g.args.length := List.toFinset_card_of_nodup hwf.1
      _ ≤ 2 := hlen
  omega

/-- The *roots* after the first `k` gates: the gate vertices among them that none of them
reads. -/
def rootSet (k : ℕ) : Finset ℕ :=
  (Finset.Ico n (n + k)).filter fun v => fanoutIn (C.gates.take k) v = 0

/-- The first `k` gates form an acyclic gate list. -/
private theorem gatesAcyclic_take (k : ℕ) : GatesAcyclic n (C.gates.take k) :=
  (gatesAcyclic_append.mp (by rw [List.take_append_drop]; exact C.args_lt)).1

/-- The roots after `k + 1` gates: those after `k` gates not read by gate `k`, and gate `k`
itself.

**Proof sketch.** The fan-out within the first `k + 1` gates is the fan-out within the
first `k` plus one if gate `k` reads the vertex.  Vertex `n + k` is read by neither (by
acyclicity), and any other vertex of the range is below `n + k`. -/
private theorem rootSet_succ {k : ℕ} (hk : k < C.gates.length) :
    C.rootSet (k + 1) =
      insert (n + k) ((C.rootSet k).filter fun v => v ∉ (C.gates[k]).args) := by
  classical
  have htake : C.gates.take (k + 1) = C.gates.take k ++ [C.gates[k]] :=
    List.take_succ_eq_append_getElem hk
  have hnk : fanoutIn (C.gates.take k) (n + k) = 0 :=
    fanoutIn_eq_zero_of_le (C.gatesAcyclic_take k) (by simp only [List.length_take]; omega)
  have hnk' : n + k ∉ (C.gates[k]).args := fun h => by have := C.args_lt k hk _ h; omega
  ext v
  simp only [rootSet, Finset.mem_filter, Finset.mem_Ico, Finset.mem_insert, htake,
    fanoutIn_append, fanoutIn_singleton]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    by_cases hv : v = n + k
    · exact Or.inl hv
    · right
      by_cases hm : v ∈ (C.gates[k]).args
      · rw [if_pos hm] at h3; omega
      · rw [if_neg hm] at h3
        exact ⟨⟨⟨h1, by omega⟩, by omega⟩, hm⟩
  · rintro (rfl | ⟨⟨⟨h1, h2⟩, h3⟩, hm⟩)
    · exact ⟨⟨by omega, by omega⟩, by rw [hnk, if_neg hnk']⟩
    · exact ⟨⟨h1, by omega⟩, by rw [h3, if_neg hm]⟩

/-- **The root-sum invariant.**  In a fan-in-two circuit whose gates have fan-out at most
one, the unfoldings of the roots after `k` gates have at most `3k` nodes in total.

**Proof sketch.** Induction on `k`.  Gate `k` reads at most two vertices; each gate vertex
`a` it reads has fan-out at most one in the whole circuit, hence was unread by the first
`k` gates, i.e. a root.  Appending gate `k` removes those roots and adds `n + k`, whose
unfolding has at most `3` nodes besides theirs (`unfoldSize_gate_le`).  So the total grows
by at most `3`. -/
theorem sum_rootSet_le (hC : C.IsFaninTwo) (hfo : ∀ v, n ≤ v → C.fanout v ≤ 1) :
    ∀ k, k ≤ C.gates.length → ∑ v ∈ C.rootSet k, C.unfoldSize v ≤ 3 * k
  | 0, _ => by simp [rootSet]
  | k + 1, hk => by
    classical
    have hk' : k < C.gates.length := by omega
    have ih := sum_rootSet_le hC hfo k hk'.le
    rw [C.rootSet_succ hk', Finset.sum_insert (by simp [rootSet])]
    set g := C.gates[k] with hg
    -- the roots read by gate `k` are exactly its gate inputs
    have hread : (C.rootSet k).filter (fun v => v ∈ g.args) = g.args.toFinset.filter (n ≤ ·) := by
      ext v
      simp only [rootSet, Finset.mem_filter, Finset.mem_Ico, List.mem_toFinset]
      constructor
      · rintro ⟨⟨⟨h1, _⟩, _⟩, hm⟩
        exact ⟨hm, h1⟩
      · rintro ⟨hm, h1⟩
        refine ⟨⟨⟨h1, C.args_lt k hk' v hm⟩, ?_⟩, hm⟩
        have hall : C.fanout v = fanoutIn (C.gates.take k) v + 1 +
            fanoutIn (C.gates.drop (k + 1)) v := by
          conv_lhs => rw [DAGCircuit.fanout, ← List.take_append_drop (k + 1) C.gates]
          rw [fanoutIn_append, List.take_succ_eq_append_getElem hk', fanoutIn_append,
            fanoutIn_singleton, if_pos hm]
        have := hfo v h1
        omega
    have hsplit := Finset.sum_filter_add_sum_filter_not (C.rootSet k) (fun v => v ∈ g.args)
      C.unfoldSize
    rw [hread] at hsplit
    have hgate := C.unfoldSize_gate_le hC hk'
    rw [← hg] at hgate
    omega

/-- **Fan-out-one circuits unfold linearly.**  The formula unfolding a fan-in-two circuit
whose gate vertices all have fan-out at most one has at most `3 · #gates + 1` nodes.
[AB09, p. 108]

**Proof sketch.** If the output is an input, the unfolding is one literal.  Otherwise the
output is gate vertex `n + k`, a root after `k + 1` gates (`rootSet_succ`), so its
unfolding is bounded by the root sum, at most `3(k + 1) ≤ 3 · #gates`
(`sum_rootSet_le`). -/
theorem toTree_size_le_of_fanout_le_one (hC : C.IsFaninTwo)
    (hfo : ∀ v, n ≤ v → C.fanout v ≤ 1) : C.toTree.size ≤ 3 * C.gates.length + 1 := by
  have hT : C.toTree.size = C.unfoldSize C.output := rfl
  rw [hT]
  by_cases ho : C.output < n
  · rw [C.unfoldSize_input ho]; omega
  · obtain ⟨k, hk⟩ : ∃ k, C.output = n + k := ⟨C.output - n, by omega⟩
    have hkl : k < C.gates.length := by have := C.output_lt; omega
    have hmem : C.output ∈ C.rootSet (k + 1) := by
      rw [C.rootSet_succ hkl, hk]; exact Finset.mem_insert_self _ _
    have hsum := C.sum_rootSet_le hC hfo (k + 1) hkl
    have := Finset.single_le_sum (f := C.unfoldSize) (fun _ _ => Nat.zero_le _) hmem
    omega

/-- **Fan-out-one circuits are formulas.**  A fan-in-two circuit whose gate vertices all
have fan-out at most one computes the same function as a fan-in-two formula with at most
`3 · #gates + 1 ≤ 4 · |C|` nodes.  [AB09, p. 108] (the converse of
`TreeCircuit.exists_dagCircuit_fanout_le_one`) -/
theorem exists_treeCircuit_of_fanout_le_one (hC : C.IsFaninTwo)
    (hfo : ∀ v, n ≤ v → C.fanout v ≤ 1) :
    ∃ t : TreeCircuit n, (∀ x, t.eval x = C.eval x) ∧ t.maxFanin ≤ 2 ∧
      t.size ≤ 3 * C.gates.length + 1 ∧ t.size ≤ 4 * C.size := by
  have h := C.toTree_size_le_of_fanout_le_one hC hfo
  have hpos : 1 ≤ C.size := by have := C.output_lt; unfold DAGCircuit.size; omega
  refine ⟨C.toTree, C.toTree_eval hC.1, C.toTree_maxFanin_le hC.1 hC.2, h, ?_⟩
  unfold DAGCircuit.size at hpos ⊢
  omega

end DAGCircuit

end BoolCircuit
