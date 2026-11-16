/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.Nat.Log
import TCSlib.Complexity.CircuitComplexity.TreeDAG

/-!
# Rewriting the gates of a DAG circuit

A generic pass that replaces every gate of a `BoolCircuit.DAGCircuit` by a small *gadget*
of new gates, in order, keeping a map from old vertices to the new vertices that compute
them.  Two instances:

* **Binarization** (`BoolCircuit.DAGCircuit.binarize`): every `∧`/`∨` gate of fan-in `k`
  becomes a balanced tree of fan-in-two gates of depth `⌈log₂ k⌉`.  Depth is multiplied by
  at most `⌈log₂ K⌉ + 1` for fan-in bound `K`, which gives `AC^i ⊆ NC^{i+1}`.
* **De Morgan** (`BoolCircuit.DAGCircuit.deMorgan`): every `∨` gate becomes
  `¬ ∧ ¬`, leaving only `∧` and `¬`, the gates of the layered model's standard basis.

## Main definitions

* `BoolCircuit.rewriteGates` — the generic pass; `BoolCircuit.GadgetSpec` — what a gadget
  must guarantee.
* `BoolCircuit.DAGCircuit.binarize`, `BoolCircuit.DAGCircuit.deMorgan`.

## Main results

* `BoolCircuit.DAGCircuit.binarize_eval`, `binarize_isFaninTwo`, `binarize_size_le`,
  `binarize_depth_le`.
* `BoolCircuit.DAGCircuit.deMorgan_eval`, `deMorgan_isWellFormed`, `deMorgan_kind`,
  `deMorgan_size_le`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.7.1, p. 118: reducing fan-in for
  `AC^i ⊆ NC^{i+1}`.)
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

variable {n : ℕ}

/-! ## Gadgets -/

/-- What a gadget must guarantee when it compiles the gate `g` after the gates `gs`:
it only appends, keeps acyclicity, returns a vertex computing `g`, adds at most `cost`
gates, adds at most `c` to the depth, and every new gate satisfies `P`. -/
structure GadgetSpec (n c cost : ℕ) (P : DAGGate → Prop) (g : DAGGate) (gs : List DAGGate)
    (r : List DAGGate × ℕ) : Prop where
  extends_gates : ∃ ext, r.1 = gs ++ ext
  acyclic : GatesAcyclic n r.1
  vertex_lt : r.2 < n + r.1.length
  value : ∀ x : Fin n → Bool,
    vertexValue r.1 x r.2 = g.eval (runWith DAGGate.eval gs (List.ofFn x))
  length_le : r.1.length ≤ gs.length + cost
  depth_le : vertexDepth n r.1 r.2 ≤ c + (g.args.map (vertexDepth n gs)).foldr max 0
  new_gates : ∀ h ∈ r.1.drop gs.length, P h

/-- A correct gadget: for every gate whose inputs are existing vertices and whose kind and
fan-in satisfy `Q`, it meets `GadgetSpec` with cost `g.args.length + 2`. -/
def GadgetCorrect (n c : ℕ) (Q : GateKind → ℕ → Prop) (P : DAGGate → Prop)
    (emit : DAGGate → List DAGGate → List DAGGate × ℕ) : Prop :=
  ∀ g gs, GatesAcyclic n gs → (∀ a ∈ g.args, a < n + gs.length) → Q g.kind g.args.length →
    GadgetSpec n c (g.args.length + 2) P g gs (emit g gs)

/-! ## The rewriting pass -/

/-- Rewrite one old gate: remap its inputs through `m`, then emit its gadget. -/
def rewriteStep (emit : DAGGate → List DAGGate → List DAGGate × ℕ)
    (s : List DAGGate × List ℕ) (g : DAGGate) : List DAGGate × List ℕ :=
  let r := emit ⟨g.kind, g.args.map fun a => s.2.getD a 0⟩ s.1
  (r.1, s.2 ++ [r.2])

/-- Rewrite a gate list: the new gates, and the new vertex of every old vertex. -/
def rewriteGates (n : ℕ) (emit : DAGGate → List DAGGate → List DAGGate × ℕ)
    (old : List DAGGate) : List DAGGate × List ℕ :=
  old.foldl (rewriteStep emit) ([], List.range n)

/-- The invariant of the rewriting pass after the old gates `old`. -/
structure RewriteInv (n c : ℕ) (P : DAGGate → Prop) (old : List DAGGate)
    (s : List DAGGate × List ℕ) : Prop where
  map_length : s.2.length = n + old.length
  map_lt : ∀ v < n + old.length, s.2.getD v 0 < n + s.1.length
  acyclic : GatesAcyclic n s.1
  value : ∀ x : Fin n → Bool, ∀ v < n + old.length,
    vertexValue s.1 x (s.2.getD v 0) = (runWith DAGGate.eval old (List.ofFn x)).getD v false
  depth : ∀ v < n + old.length,
    vertexDepth n s.1 (s.2.getD v 0) ≤
      c * (runWith DAGGate.depth old (List.replicate n 0)).getD v 0
  length_le : s.1.length ≤ (old.map fun g => g.args.length + 2).sum
  new_gates : ∀ h ∈ s.1, P h

private theorem foldr_max_le' {l : List ℕ} {f : ℕ → ℕ} {B : ℕ} (h : ∀ a ∈ l, f a ≤ B) :
    (l.map f).foldr max 0 ≤ B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

private theorem le_foldr_max' {l : List ℕ} {f : ℕ → ℕ} {a : ℕ} (ha : a ∈ l) :
    f a ≤ (l.map f).foldr max 0 := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp ha with rfl | ha
    · exact le_max_left _ _
    · exact (ih ha).trans (le_max_right _ _)

/-- The rewriting invariant holds at the start: with no old gates processed, the empty
new gate list and the identity vertex map `0, …, n - 1` satisfy `RewriteInv` (each input
vertex maps to itself, with the same value and depth `0`). -/
theorem rewriteInv_nil (c : ℕ) (P : DAGGate → Prop) :
    RewriteInv n c P [] ([], List.range n) := by
  refine ⟨by simp, fun v hv => ?_, GatesAcyclic.nil, fun x v hv => ?_, fun v hv => ?_, by simp,
    by simp⟩
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_range (by simpa using hv)]; simpa
    using hv
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_range (by simpa using hv),
      Option.getD_some]
    have := vertexValue_input ([] : List DAGGate) x ⟨v, by simpa using hv⟩
    simp_all [vertexValue]
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_range (by simpa using hv),
      Option.getD_some]
    have := vertexDepth_input (n := n) ([] : List DAGGate) (i := v) (by simpa using hv)
    simp [vertexDepth] at this ⊢

/-- One rewriting step preserves the invariant.

**Proof sketch.** Remap the new old gate `g`'s arguments through the current vertex
map to get `g'`, whose arguments are existing new vertices, and apply the gadget
specification to `g'`.  The gadget only appends gates, so every previously mapped vertex
keeps its value and depth, and appending `g` to the old list likewise leaves earlier old
vertices unchanged.  For the new vertex: its value is `g'` evaluated on new values, which
by the invariant equal the old values `g` reads, hence `g`'s value.  Its depth is at most
`c` plus the deepest remapped argument, which by the invariant is at most `c` times the
deepest old argument, giving `c * (that + 1)`.  Gate-count and the predicate `P` add up
from the gadget's cost and new-gate guarantees. -/
theorem rewriteInv_step {c : ℕ} {Q : GateKind → ℕ → Prop} {P : DAGGate → Prop}
    {emit : DAGGate → List DAGGate → List DAGGate × ℕ} (hemit : GadgetCorrect n c Q P emit)
    {old : List DAGGate} {g : DAGGate} {s : List DAGGate × List ℕ}
    (hinv : RewriteInv n c P old s) (hold : GatesAcyclic n (old ++ [g]))
    (hQ : Q g.kind g.args.length) :
    RewriteInv n c P (old ++ [g]) (rewriteStep emit s g) := by
  obtain ⟨hml, hmlt, hac, hval, hdep, hlen, hnew⟩ := hinv
  have hglt : ∀ a ∈ g.args, a < n + old.length := by
    intro a ha
    have := hold old.length (by simp) a (by simpa using ha)
    exact this
  set g' : DAGGate := ⟨g.kind, g.args.map fun a => s.2.getD a 0⟩ with hg'
  have hspec := hemit g' s.1 hac (by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact hmlt b (hglt b hb)) (by simpa [hg'] using hQ)
  set r := emit g' s.1 with hr
  obtain ⟨ext, hext⟩ := hspec.extends_gates
  have hstep : rewriteStep emit s g = (r.1, s.2 ++ [r.2]) := rfl
  rw [hstep]
  have hlen_old : n + (old ++ [g]).length = n + old.length + 1 := by simp; omega
  have hgetD_old : ∀ v < n + old.length, (s.2 ++ [r.2]).getD v 0 = s.2.getD v 0 := fun v hv =>
    List.getD_append _ _ _ _ (by omega)
  have hgetD_new : (s.2 ++ [r.2]).getD (n + old.length) 0 = r.2 := by
    rw [List.getD_append_right _ _ _ _ (by omega)]; simp [hml]
  -- old vertex values and depths are unchanged by the new old-gate
  have hold_val : ∀ x v, v < n + old.length →
      (runWith DAGGate.eval (old ++ [g]) (List.ofFn x)).getD v false =
        (runWith DAGGate.eval old (List.ofFn x)).getD v false := fun x v hv => by
    rw [runWith_append, runWith_getD_of_lt]; simpa using hv
  have hold_dep : ∀ v, v < n + old.length →
      (runWith DAGGate.depth (old ++ [g]) (List.replicate n 0)).getD v 0 =
        (runWith DAGGate.depth old (List.replicate n 0)).getD v 0 := fun v hv => by
    rw [runWith_append, runWith_getD_of_lt]; simpa using hv
  have hnew_val : ∀ x, (runWith DAGGate.eval (old ++ [g]) (List.ofFn x)).getD
      (n + old.length) false = g.eval (runWith DAGGate.eval old (List.ofFn x)) := fun x => by
    have := runWith_getD_last DAGGate.eval old g (List.ofFn x) false
    rwa [List.length_ofFn] at this
  have hnew_dep : (runWith DAGGate.depth (old ++ [g]) (List.replicate n 0)).getD
      (n + old.length) 0 = g.depth (runWith DAGGate.depth old (List.replicate n 0)) := by
    have := runWith_getD_last DAGGate.depth old g (List.replicate n 0) 0
    rwa [List.length_replicate] at this
  refine ⟨by simp [hml]; omega, fun v hv => ?_, hspec.acyclic, fun x v hv => ?_,
    fun v hv => ?_, ?_, ?_⟩
  · rw [hlen_old] at hv
    rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hv | rfl
    · rw [hgetD_old v hv]
      exact lt_of_lt_of_le (hmlt v hv) (by rw [hext]; simp)
    · rw [hgetD_new]; exact hspec.vertex_lt
  · rw [hlen_old] at hv
    rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hv | rfl
    · rw [hgetD_old v hv, hold_val x v hv, hext, vertexValue_append _ _ _ (hmlt v hv)]
      exact hval x v hv
    · rw [hgetD_new, hspec.value x, hnew_val x]
      -- the remapped gate reads the same values as the old gate
      exact DAGGate.eval_remap g _ fun a ha => hval x a (hglt a ha)
  · rw [hlen_old] at hv
    rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hv | rfl
    · rw [hgetD_old v hv, hold_dep v hv, hext, vertexDepth_append _ _ (hmlt v hv)]
      exact hdep v hv
    · rw [hgetD_new, hnew_dep]
      refine hspec.depth_le.trans ?_
      simp only [hg', List.map_map, Function.comp_def, DAGGate.depth]
      have : ((g.args.map fun a => vertexDepth n s.1 (s.2.getD a 0))).foldr max 0 ≤
          c * (g.args.map fun a =>
            (runWith DAGGate.depth old (List.replicate n 0)).getD a 0).foldr max 0 :=
        foldr_max_le' fun a ha => (hdep a (hglt a ha)).trans
          (Nat.mul_le_mul_left c (le_foldr_max' (f := fun a =>
            (runWith DAGGate.depth old (List.replicate n 0)).getD a 0) ha))
      rw [Nat.mul_add, Nat.mul_one]
      omega
  · have := hspec.length_le
    simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    have : g'.args.length = g.args.length := by simp [hg']
    omega
  · intro h hh
    rw [hext, List.mem_append] at hh
    rcases hh with hh | hh
    · exact hnew h hh
    · exact hspec.new_gates h (by rw [hext]; simpa using hh)

/-- The invariant holds after rewriting any acyclic gate list. -/
theorem rewriteGates_inv {c : ℕ} {Q : GateKind → ℕ → Prop} {P : DAGGate → Prop}
    {emit : DAGGate → List DAGGate → List DAGGate × ℕ} (hemit : GadgetCorrect n c Q P emit) :
    ∀ (old : List DAGGate), GatesAcyclic n old → (∀ g ∈ old, Q g.kind g.args.length) →
      RewriteInv n c P old (rewriteGates n emit old) := by
  intro old
  induction old using List.reverseRecOn with
  | nil => intro _ _; exact rewriteInv_nil c P
  | append_singleton old g ih =>
    intro hac hnot
    have hac' : GatesAcyclic n old := fun i hi a ha => by
      have := hac i (by simp; omega) a (by rwa [List.getElem_append_left hi])
      exact this
    have := ih hac' fun g' hg' => hnot g' (by simp [hg'])
    rw [rewriteGates, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact rewriteInv_step hemit this hac (hnot g (by simp))

/-- The rewritten circuit. -/
def DAGCircuit.rewrite (C : DAGCircuit n) {c : ℕ} {Q : GateKind → ℕ → Prop}
    {P : DAGGate → Prop} (emit : DAGGate → List DAGGate → List DAGGate × ℕ)
    (hemit : GadgetCorrect n c Q P emit) (hnot : ∀ g ∈ C.gates, Q g.kind g.args.length) :
    DAGCircuit n where
  gates := (rewriteGates n emit C.gates).1
  output := (rewriteGates n emit C.gates).2.getD C.output 0
  args_lt := (rewriteGates_inv hemit C.gates C.args_lt hnot).acyclic
  output_lt := (rewriteGates_inv hemit C.gates C.args_lt hnot).map_lt _ C.output_lt

section Rewrite

variable (C : DAGCircuit n) {c : ℕ} {Q : GateKind → ℕ → Prop} {P : DAGGate → Prop}
  (emit : DAGGate → List DAGGate → List DAGGate × ℕ) (hemit : GadgetCorrect n c Q P emit)
  (hnot : ∀ g ∈ C.gates, Q g.kind g.args.length)

/-- Rewriting a DAG circuit gate by gate with a correct gadget preserves its Boolean
function: `(C.rewrite emit …).eval x = C.eval x` for every input `x`. -/
theorem DAGCircuit.rewrite_eval (x : Fin n → Bool) :
    (C.rewrite emit hemit hnot).eval x = C.eval x :=
  (rewriteGates_inv hemit C.gates C.args_lt hnot).value x _ C.output_lt

/-- Rewriting with a gadget that adds at most `c` levels per gate multiplies depth by at
most `c`: the rewritten circuit has depth at most `c * C.depth`. -/
theorem DAGCircuit.rewrite_depth_le : (C.rewrite emit hemit hnot).depth ≤ c * C.depth :=
  (rewriteGates_inv hemit C.gates C.args_lt hnot).depth _ C.output_lt

/-- Every gate of the rewritten circuit satisfies the gadget's output predicate `P`. -/
theorem DAGCircuit.rewrite_new_gates : ∀ h ∈ (C.rewrite emit hemit hnot).gates, P h :=
  (rewriteGates_inv hemit C.gates C.args_lt hnot).new_gates

/-- The rewritten circuit has at most `∑ (fan-in + 2)` gates, summed over the gates of
the original circuit. -/
theorem DAGCircuit.rewrite_length_le :
    (C.rewrite emit hemit hnot).gates.length ≤ (C.gates.map fun g => g.args.length + 2).sum :=
  (rewriteGates_inv hemit C.gates C.args_lt hnot).length_le

end Rewrite

/-- Each old gate costs at most its fan-in plus two, so with fan-in at most `size` the
rewritten gate list has at most `#gates * (size + 2)` gates. -/
theorem DAGCircuit.sum_cost_le (C : DAGCircuit n) (hk : ∀ g ∈ C.gates, g.args.length ≤ C.size) :
    (C.gates.map fun g => g.args.length + 2).sum ≤ C.gates.length * (C.size + 2) := by
  generalize C.gates = gs at hk ⊢
  induction gs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have := hk g (by simp); have := ih fun g' hg' => hk g' (by simp [hg']); omega

end BoolCircuit
