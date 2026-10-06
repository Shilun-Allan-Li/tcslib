/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Computability.Language
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.DeriveFintype

/-!
# Boolean circuits as directed acyclic graphs

The circuit model of [AB09, Def 6.1]: a directed acyclic graph with `n` source vertices
(the inputs) and one sink (the output), whose other vertices are gates labelled `∧`, `∨`
or `¬`.  Vertices are **numbered topologically**: the inputs are vertices `0, …, n - 1`,
gate `i` is vertex `n + i`, and a gate reads only vertices numbered below it, which is
exactly acyclicity.  Gates may feed any number of later gates (unbounded fan-out).

This is the model the book's circuit classes are stated over; `PPoly.lean` defines
`SIZE` and `P/poly` on it and `NCAC.lean` defines `NC` and `AC`.  The two other circuit
models of the library are `BoolCircuit.TreeCircuit` (formulas: fan-out one, negation only
at the inputs) and `BoolCircuit.LayeredCircuit` (layered DAGs over an arbitrary gate set,
the carrier of the Razborov–Smolensky development); the conversions are in `TreeDAG.lean`
and `LayeredDAG.lean`.

## Main definitions

* `BoolCircuit.GateKind`, `BoolCircuit.DAGGate` — a gate label and a gate.
* `BoolCircuit.DAGCircuit n` — a circuit with `n` inputs, with `eval`, `size` (the number
  of vertices, inputs included, as in [AB09, Def 6.1]) and `depth` (the length of the
  longest input-to-output path).
* `BoolCircuit.DAGCircuit.IsWellFormed` — `¬` gates have exactly one input and no gate
  reads a vertex twice (the graph has no parallel edges).
* `BoolCircuit.DAGCircuit.IsFaninTwo` — well formed, and every gate has at most two inputs.
* `BoolCircuit.DAGCircuitFamily` — one circuit per input length, with `language`,
  `IsPolySize`, `HasFaninTwo`, `IsWellFormed` and `HasPolylogDepth`.
* `BoolCircuit.GatesAcyclic` — a bare gate list reads only earlier vertices (the
  acyclicity field of `DAGCircuit`); `BoolCircuit.DAGGate.WellFormed`,
  `BoolCircuit.DAGGate.FaninTwo` — the gate-level well-formedness predicates.
* `BoolCircuit.constGate`, `BoolCircuit.constCircuit` — the model's constant gates
  (fan-in-zero `∧`/`∨`) and constant circuits.
* `BoolCircuit.DAGGate.remap` — rename the vertices a gate reads.

## Main results

* `BoolCircuit.runWith_getD_gate` — the value (or depth) of gate `i` is computed from the
  vertices before it; `BoolCircuit.runWith_getD_of_lt` — appending gates never changes
  the value of an existing vertex.  These two facts drive every proof about the model.
* `BoolCircuit.DAGCircuit.values_getD_gate`, `BoolCircuit.DAGCircuit.depthAt_gate` — the
  evaluation and depth recurrences at a gate vertex.
* `BoolCircuit.DAGGate.eval_remap`, `BoolCircuit.runWith_remap_rel` — renaming vertices
  commutes with evaluation, gate by gate and along a whole gate list.
* `BoolCircuit.gatesAcyclic_append`, `BoolCircuit.gatesAcyclic_cons` — acyclicity of
  concatenations.

## Divergences from [AB09, Def 6.1]

* **`∧`/`∨` fan-in is at most two, not exactly two.**  [AB09] gives every `∧`/`∨` gate
  fan-in `2` and has no constants.  Taken literally, a circuit on `0` inputs has no
  vertex to output, so no language would be decidable at length `0`; allowing fan-in `0`
  gives the constants (`∧` of nothing is `true`, `∨` of nothing is `false`), and fan-in `1`
  is an identity gate that can always be bypassed.  The literal model is
  `BoolCircuit.DAGCircuit.IsStrict` (`StrictCircuit.lean`).  It has no circuit at all on
  `0` inputs (`DAGCircuit.not_isStrict_zero`).  For `n ≥ 1` the relaxation costs a
  constant factor: `DAGCircuit.exists_isStrict` (`StrictSize.lean`) turns a fan-in-two
  circuit of size `S` into a strict one of size `≤ 4S + 12`.  That circuit has no constants
  or identity gates, and its output is the only sink, so unused gates and inputs are
  attached as well.  `Language.inPPoly_iff_inStrictPPoly` shows `P/poly` is unchanged.
* **Single output, as in the book.**  [AB09, Def 6.1] is single-output; the multi-output
  generalization is only a remark on p. 107 ("it is trivial to generalize the
  definition … though we typically will not need this generalization").  Multi-output
  circuits, where needed (Karp–Lipton, p. 114), are `BoolCircuit.MultiDAGCircuit`.
* **Gates not reaching the output are allowed (divergence).**  [AB09, Def 6.1] demands
  exactly one sink, so every gate of a book circuit lies on a path to the output.  Here
  the output is a designated vertex and other gates may be sinks; they are counted in
  `size`.  The divergence is harmless for every size bound: deleting the gates that do
  not reach the output preserves the computed function and only shrinks the size, so
  dead gates never help an upper bound, and a lower bound here is at least as strong.
  (An unread *input* would also be a second sink under the book's definition.)  The formal
  bridge to the single-sink model is `DAGCircuit.seal` and `DAGCircuit.exists_isStrict`
  (`StrictSize.lean`), which supersede pruning: they attach every dead vertex, unread
  inputs included, neutrally to the output, at linear cost.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, Definitions 6.1 and 6.2.)
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

/-- The label of a gate: `∧`, `∨` or `¬`.  [AB09, Def 6.1] -/
inductive GateKind where
  | and
  | or
  | not
  deriving DecidableEq, Repr, Fintype

/-- A gate: its label and the vertices it reads, in order. -/
structure DAGGate where
  /-- The gate's label. -/
  kind : GateKind
  /-- The vertices whose values the gate reads. -/
  args : List ℕ
  deriving DecidableEq, Repr

namespace DAGGate

/-- Evaluate a gate, reading vertex `v`'s value as `vals.getD v false`.  A `¬` gate
negates the conjunction of its inputs, which is the negation of its single input in a
well-formed circuit. -/
def eval (g : DAGGate) (vals : List Bool) : Bool :=
  match g.kind with
  | .and => g.args.all fun a => vals.getD a false
  | .or => g.args.any fun a => vals.getD a false
  | .not => !(g.args.all fun a => vals.getD a false)

/-- The depth of a gate: one more than the deepest vertex it reads, vertex `v`'s depth
being `ds.getD v 0`. -/
def depth (g : DAGGate) (ds : List ℕ) : ℕ :=
  1 + (g.args.map fun a => ds.getD a 0).foldr max 0

end DAGGate

/-! ## Running a gate list -/

/-- Run a gate list from initial vertex data `init`: each gate appends `f g vs`, computed
from the data `vs` of all earlier vertices.  `DAGCircuit.values` and `DAGCircuit.depths`
are the two instances. -/
def runWith {β : Type} (f : DAGGate → List β → β) (gs : List DAGGate) (init : List β) :
    List β :=
  gs.foldl (fun vs g => vs ++ [f g vs]) init

section RunWith

variable {β : Type} (f : DAGGate → List β → β)

/-- Running the empty gate list leaves the initial vertex data unchanged. -/
@[simp] theorem runWith_nil (init : List β) : runWith f [] init = init := rfl

/-- Running `g :: gs` from `init` is running `gs` from `init` extended by the datum `f g init`
of the first gate. -/
theorem runWith_cons (g : DAGGate) (gs : List DAGGate) (init : List β) :
    runWith f (g :: gs) init = runWith f gs (init ++ [f g init]) := rfl

/-- Running a concatenation `gs ++ hs` is running `hs` from the result of running `gs`. -/
theorem runWith_append (gs hs : List DAGGate) (init : List β) :
    runWith f (gs ++ hs) init = runWith f hs (runWith f gs init) := by
  simp [runWith, List.foldl_append]

/-- Running a single gate `g` from `init` appends exactly the datum `f g init`. -/
theorem runWith_singleton (g : DAGGate) (init : List β) :
    runWith f [g] init = init ++ [f g init] := rfl

/-- Running a gate list appends one datum per gate: the result has length
`init.length + gs.length`. -/
@[simp] theorem length_runWith (gs : List DAGGate) (init : List β) :
    (runWith f gs init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih => rw [runWith_cons, ih]; simp; omega

/-- Running more gates only appends: the old data is a prefix. -/
theorem runWith_eq_append (gs : List DAGGate) (init : List β) :
    ∃ ext, runWith f gs init = init ++ ext := by
  induction gs generalizing init with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨ext, h⟩ := ih (init ++ [f g init])
    exact ⟨[f g init] ++ ext, by rw [runWith_cons, h, List.append_assoc]⟩

/-- Appending gates never changes the data of an existing vertex. -/
theorem runWith_getD_of_lt (gs : List DAGGate) (init : List β) {v : ℕ} (hv : v < init.length)
    (d : β) : (runWith f gs init).getD v d = init.getD v d := by
  obtain ⟨ext, h⟩ := runWith_eq_append f gs init
  rw [h, List.getD_append _ _ _ _ hv]

/-- The data of the last gate of a list. -/
theorem runWith_getD_last (gs : List DAGGate) (g : DAGGate) (init : List β) (d : β) :
    (runWith f (gs ++ [g]) init).getD (init.length + gs.length) d =
      f g (runWith f gs init) := by
  rw [runWith_append, runWith_singleton]
  have : (runWith f gs init).length = init.length + gs.length := length_runWith f gs init
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp [this]

/-- The data of gate `i` is computed from the vertices before it. -/
theorem runWith_getD_gate (gs : List DAGGate) (init : List β) {i : ℕ} (hi : i < gs.length)
    (d : β) :
    (runWith f gs init).getD (init.length + i) d = f gs[i] (runWith f (gs.take i) init) := by
  have hlen : (gs.take i).length = i := List.length_take_of_le hi.le
  have hsplit : runWith f gs init =
      runWith f (gs.drop (i + 1)) (runWith f (gs.take i ++ [gs[i]]) init) := by
    rw [← runWith_append, List.append_assoc, List.singleton_append,
      ← List.drop_eq_getElem_cons hi, List.take_append_drop]
  rw [hsplit, runWith_getD_of_lt]
  · have := runWith_getD_last f (gs.take i) gs[i] init d
    rwa [hlen] at this
  · simp [hi]

/-- Reading only vertices below `k` gives the same data before and after more gates. -/
theorem runWith_getD_take (gs : List DAGGate) (init : List β) {i a : ℕ}
    (hi : i ≤ gs.length) (ha : a < init.length + i) (d : β) :
    (runWith f (gs.take i) init).getD a d = (runWith f gs init).getD a d := by
  conv_rhs => rw [← List.take_append_drop i gs, runWith_append]
  rw [runWith_getD_of_lt f (gs.drop i) (runWith f (gs.take i) init)
    (by rw [length_runWith, List.length_take_of_le hi]; exact ha)]

end RunWith

/-! ## Circuits -/

/-- `List.all` depends only on the predicate's values on the list's members. -/
theorem all_congr_mem {α : Type} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, h a (by simp), ih (fun b hb => h b (by simp [hb]))]

/-- `List.any` depends only on the predicate's values on the list's members. -/
theorem any_congr_mem {α : Type} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons, h a (by simp), ih (fun b hb => h b (by simp [hb]))]

/-- A gate's value depends only on the values of the vertices it reads. -/
theorem DAGGate.eval_congr (g : DAGGate) {vals vals' : List Bool}
    (h : ∀ a ∈ g.args, vals.getD a false = vals'.getD a false) :
    g.eval vals = g.eval vals' := by
  unfold DAGGate.eval
  split
  · exact all_congr_mem h
  · exact any_congr_mem h
  · rw [all_congr_mem h]

/-- A gate's depth depends only on the depths of the vertices it reads. -/
theorem DAGGate.depth_congr (g : DAGGate) {ds ds' : List ℕ}
    (h : ∀ a ∈ g.args, ds.getD a 0 = ds'.getD a 0) :
    g.depth ds = g.depth ds' := by
  unfold DAGGate.depth
  rw [List.map_congr_left h]

/-! ## Gate predicates, constant gates and renamed gates -/

/-- A gate is well formed: no repeated input, and `¬` reads exactly one vertex.  A circuit
is `DAGCircuit.IsWellFormed` iff all its gates are. -/
def DAGGate.WellFormed (g : DAGGate) : Prop :=
  g.args.Nodup ∧ (g.kind = .not → g.args.length = 1)

/-- A gate admissible in a fan-in-two circuit: well formed, reading at most two
vertices. -/
def DAGGate.FaninTwo (g : DAGGate) : Prop :=
  g.WellFormed ∧ g.args.length ≤ 2

/-- The constant gate for the bit `b`: a fan-in-zero `∧` (value `true`) if `b`, a
fan-in-zero `∨` (value `false`) otherwise.  These are the model's constants (see the
fan-in divergence in the module docstring). -/
def constGate (b : Bool) : DAGGate :=
  ⟨if b then .and else .or, []⟩

/-- The constant-`1` gate is the fan-in-zero `∧`. -/
theorem constGate_true : constGate true = ⟨.and, []⟩ := rfl

/-- The constant-`0` gate is the fan-in-zero `∨`. -/
theorem constGate_false : constGate false = ⟨.or, []⟩ := rfl

/-- A constant gate evaluates to its bit, whatever the vertex values. -/
@[simp] theorem constGate_eval (b : Bool) (vals : List Bool) : (constGate b).eval vals = b := by
  cases b <;> rfl

/-- A constant gate has depth `1`. -/
@[simp] theorem constGate_depth (b : Bool) (ds : List ℕ) : (constGate b).depth ds = 1 := by
  cases b <;> rfl

/-- A constant gate reads no vertex. -/
@[simp] theorem constGate_args (b : Bool) : (constGate b).args = [] := rfl

/-- A constant gate is not a `¬` gate. -/
theorem constGate_kind_ne_not (b : Bool) : (constGate b).kind ≠ .not := by
  cases b <;> simp [constGate]

/-- A constant gate is admissible in a fan-in-two circuit. -/
@[simp] theorem constGate_faninTwo (b : Bool) : (constGate b).FaninTwo :=
  ⟨⟨by simp, fun h => absurd h (constGate_kind_ne_not b)⟩, by simp⟩

/-- The gate `g` with every input vertex `a` renamed to `σ a`. -/
def DAGGate.remap (σ : ℕ → ℕ) (g : DAGGate) : DAGGate :=
  ⟨g.kind, g.args.map σ⟩

/-- Renaming by the identity changes nothing. -/
@[simp] theorem DAGGate.remap_id (g : DAGGate) : g.remap id = g := by
  cases g; simp [DAGGate.remap]

/-- A renamed gate has the original gate's value when every renamed input carries the
original input's value. -/
theorem DAGGate.eval_remap (g : DAGGate) (σ : ℕ → ℕ) {vals vals' : List Bool}
    (h : ∀ a ∈ g.args, vals.getD (σ a) false = vals'.getD a false) :
    (g.remap σ).eval vals = g.eval vals' := by
  rcases g with ⟨k, args⟩
  have hall : ((args.map σ).all fun a => vals.getD a false) =
      args.all fun a => vals'.getD a false := by
    rw [List.all_map]; exact all_congr_mem fun a ha => by simpa using h a ha
  have hany : ((args.map σ).any fun a => vals.getD a false) =
      args.any fun a => vals'.getD a false := by
    rw [List.any_map]; exact any_congr_mem fun a ha => by simpa using h a ha
  cases k <;> simp only [DAGGate.remap, DAGGate.eval, hall, hany]

/-- **Renaming vertices commutes with running gates.**  Let `σ` send the `L` initial
vertices of `init` to vertices among the `L'` initial vertices of `init'`, and send gate
vertex `L + i` to `L' + i`.  If the gate step `f` turns a relation `R` between the data
read through `σ` and the original data into `R` between the outputs, and `R` holds
between `init'` (through `σ`) and `init`, then `R` holds at every vertex between running
the renamed gates from `init'` and running the original gates from `init`.

Technical glue with no textbook counterpart; used with `R` equality for values and
`R a b ↔ a ≤ b + 1` for depths.

**Proof sketch.** Induction on the gate list from the right.  Adding a last gate `g`
leaves the data of every earlier vertex unchanged on both sides (gates only append), and
`σ` keeps earlier vertices earlier, so the induction hypothesis covers them.  The new
vertex `L + |old|` is sent by `σ` to `L' + |old|`, where the renamed side holds
`f (g.remap σ)` of the renamed data and the original side `f g` of the original data;
every input of `g` is an earlier vertex by acyclicity, so the hypothesis on `f` applies. -/
theorem runWith_remap_rel {β : Type} (f : DAGGate → List β → β) (R : β → β → Prop) (d : β)
    (σ : ℕ → ℕ)
    (hf : ∀ (g : DAGGate) (vs vs' : List β),
      (∀ a ∈ g.args, R (vs.getD (σ a) d) (vs'.getD a d)) → R (f (g.remap σ) vs) (f g vs'))
    {L L' : ℕ} (init init' : List β) (hL : init.length = L) (hL' : init'.length = L')
    (hσ_lt : ∀ v < L, σ v < L') (hσ_gate : ∀ i, σ (L + i) = L' + i)
    (hinit : ∀ v < L, R (init'.getD (σ v) d) (init.getD v d)) (gs : List DAGGate)
    (hgs : ∀ (i : ℕ) (h : i < gs.length), ∀ a ∈ (gs[i]).args, a < L + i) :
    ∀ v < L + gs.length,
      R ((runWith f (gs.map (DAGGate.remap σ)) init').getD (σ v) d)
        ((runWith f gs init).getD v d) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro v hv
    simpa using hinit v (by simpa using hv)
  | append_singleton old g ih =>
    have hold : ∀ (i : ℕ) (h : i < old.length), ∀ a ∈ (old[i]).args, a < L + i :=
      fun i hi a ha => hgs i (by simp; omega) a (by rwa [List.getElem_append_left hi])
    have hg : ∀ a ∈ g.args, a < L + old.length := fun a ha =>
      hgs old.length (by simp) a (by simpa using ha)
    have ih := ih hold
    have hlen : (runWith f (old.map (DAGGate.remap σ)) init').length = L' + old.length := by
      simp [hL']
    have hlen0 : (runWith f old init).length = L + old.length := by simp [hL]
    -- vertices below the new gate keep their (renamed) data
    have hσ_old : ∀ v < L + old.length, σ v < L' + old.length := by
      intro v hv
      by_cases hvL : v < L
      · have := hσ_lt v hvL; omega
      · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hvL)
        rw [hσ_gate]; omega
    intro v hv
    rw [List.map_append, List.map_singleton, runWith_append, runWith_append,
      runWith_singleton, runWith_singleton]
    simp only [List.length_append, List.length_singleton] at hv
    rcases Nat.lt_succ_iff_lt_or_eq.mp (by omega : v < L + old.length + 1) with hv | rfl
    · rw [List.getD_append _ _ _ _ (by rw [hlen]; exact hσ_old v hv),
        List.getD_append _ _ _ _ (by rw [hlen0]; exact hv)]
      exact ih v hv
    · -- the new gate: its inputs carry related data by the induction hypothesis
      rw [hσ_gate, List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega), hlen, hlen0]
      simp only [Nat.sub_self, List.getD_cons_zero]
      exact hf g _ _ fun a ha => ih a (hg a ha)

/-! ## Gate lists that read only earlier vertices -/

/-- Every gate of `gs` reads only vertices below its own, `n` inputs coming first: the
acyclicity condition `DAGCircuit.args_lt` for a bare gate list. -/
def GatesAcyclic (n : ℕ) (gs : List DAGGate) : Prop :=
  ∀ (i : ℕ) (h : i < gs.length), ∀ a ∈ (gs[i]).args, a < n + i

/-- The empty gate list is acyclic. -/
theorem GatesAcyclic.nil {n : ℕ} : GatesAcyclic n [] := fun i h => absurd h (by simp)

/-- Appending a gate that reads only existing vertices keeps a gate list acyclic. -/
theorem GatesAcyclic.snoc {n : ℕ} {gs : List DAGGate} (h : GatesAcyclic n gs) {g : DAGGate}
    (hg : ∀ a ∈ g.args, a < n + gs.length) : GatesAcyclic n (gs ++ [g]) := by
  intro i hi a ha
  rw [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
  · rw [List.getElem_append_left hlt] at ha
    exact h i hlt a ha
  · simp only [List.getElem_append_right (le_refl _), Nat.sub_self,
      List.getElem_singleton] at ha
    exact hg a ha

/-- Appending a gate list that reads only vertices before each of its own gates (counted
from the end of the first list) keeps the whole list acyclic. -/
theorem GatesAcyclic.append {n : ℕ} {gs hs : List DAGGate} (hg : GatesAcyclic n gs)
    (hh : GatesAcyclic (n + gs.length) hs) : GatesAcyclic n (gs ++ hs) := by
  intro i hi a ha
  by_cases hlt : i < gs.length
  · rw [List.getElem_append_left hlt] at ha
    exact hg i hlt a ha
  · rw [List.getElem_append_right (by omega)] at ha
    have := hh (i - gs.length) (by simp at hi; omega) a ha
    omega

/-- The empty gate list is acyclic (as a `simp` rewrite). -/
@[simp] theorem gatesAcyclic_nil {n : ℕ} : GatesAcyclic n [] ↔ True :=
  iff_true_intro GatesAcyclic.nil

/-- A gate list started at vertex `n` is acyclic iff its first gate reads only vertices
below `n` and the rest, started at `n + 1`, is acyclic. -/
@[simp] theorem gatesAcyclic_cons {n : ℕ} {g : DAGGate} {gs : List DAGGate} :
    GatesAcyclic n (g :: gs) ↔ (∀ a ∈ g.args, a < n) ∧ GatesAcyclic (n + 1) gs := by
  constructor
  · intro h
    refine ⟨fun a ha => by simpa using h 0 (by simp) a (by simpa using ha), ?_⟩
    intro i hi a ha
    have := h (i + 1) (by simp; omega) a (by simpa using ha)
    omega
  · rintro ⟨h0, h⟩ i hi a ha
    cases i with
    | zero => simpa using h0 a (by simpa using ha)
    | succ i =>
      have := h i (by simpa using hi) a (by simpa using ha)
      omega

/-- A concatenation is acyclic iff the first part is, started at `n`, and the second part
is, started after the first. -/
theorem gatesAcyclic_append {n : ℕ} {gs hs : List DAGGate} :
    GatesAcyclic n (gs ++ hs) ↔ GatesAcyclic n gs ∧ GatesAcyclic (n + gs.length) hs := by
  induction gs generalizing n with
  | nil => simp
  | cons g gs ih =>
    simp only [List.cons_append, gatesAcyclic_cons, ih, List.length_cons, and_assoc]
    rw [show n + 1 + gs.length = n + (gs.length + 1) by omega]

/-- A Boolean circuit with `n` inputs and one output: a DAG whose vertices are numbered
topologically.  Vertices `0, …, n - 1` are the inputs, vertex `n + i` is gate `i`, and
gate `i` reads only vertices below `n + i`.  [AB09, Def 6.1] -/
structure DAGCircuit (n : ℕ) where
  /-- The gates, in topological order. -/
  gates : List DAGGate
  /-- The output vertex. -/
  output : ℕ
  /-- Gate `i` reads only earlier vertices: the graph is acyclic. -/
  args_lt : ∀ (i : ℕ) (h : i < gates.length), ∀ a ∈ (gates[i]).args, a < n + i
  /-- The output is a vertex of the circuit. -/
  output_lt : output < n + gates.length

namespace DAGCircuit

variable {n : ℕ} (C : DAGCircuit n)

/-- The values of all vertices on input `x`: the inputs, then each gate in order. -/
def values (x : Fin n → Bool) : List Bool :=
  runWith DAGGate.eval C.gates (List.ofFn x)

/-- The circuit's output on input `x`. -/
def eval (x : Fin n → Bool) : Bool :=
  (C.values x).getD C.output false

/-- The depths of all vertices: `0` at the inputs, one more than the deepest input at a
gate. -/
def depths : List ℕ :=
  runWith DAGGate.depth C.gates (List.replicate n 0)

/-- The depth of vertex `v`: the length of the longest path from an input to `v`. -/
def depthAt (v : ℕ) : ℕ := C.depths.getD v 0

/-- The depth of the circuit: the length of the longest path from an input to the
output.  [AB09, Def 6.1] -/
def depth : ℕ := C.depthAt C.output

/-- The size of the circuit: its number of vertices, inputs included.  [AB09, Def 6.1] -/
def size : ℕ := n + C.gates.length

/-- `¬` gates have exactly one input, and no gate reads a vertex twice. -/
def IsWellFormed : Prop :=
  ∀ g ∈ C.gates, g.args.Nodup ∧ (g.kind = .not → g.args.length = 1)

/-- Well formed, with every gate reading at most two vertices.  [AB09, Def 6.1] -/
def IsFaninTwo : Prop :=
  C.IsWellFormed ∧ ∀ g ∈ C.gates, g.args.length ≤ 2

/-- The vertex-value list of a circuit has one entry per vertex: `n` inputs plus one per
gate. -/
@[simp] theorem length_values (x : Fin n → Bool) :
    (C.values x).length = n + C.gates.length := by
  simp [values]

/-- The vertex-depth list of a circuit has one entry per vertex: `n` inputs plus one per
gate. -/
@[simp] theorem length_depths : C.depths.length = n + C.gates.length := by
  simp [depths]

/-- An input vertex holds its input bit. -/
theorem values_getD_input (x : Fin n → Bool) (i : Fin n) :
    (C.values x).getD i false = x i := by
  rw [values, runWith_getD_of_lt _ _ _ (by simp)]
  simp

/-- An input vertex has depth `0`. -/
theorem depthAt_input {i : ℕ} (hi : i < n) : C.depthAt i = 0 := by
  rw [depthAt, depths, runWith_getD_of_lt _ _ _ (by simpa using hi)]
  simp [hi]

/-- Gate `i`'s value is its gate applied to the values of all vertices. -/
theorem values_getD_gate (x : Fin n → Bool) {i : ℕ} (hi : i < C.gates.length) :
    (C.values x).getD (n + i) false = C.gates[i].eval (C.values x) := by
  have key := runWith_getD_gate DAGGate.eval C.gates (List.ofFn x) hi false
  simp only [List.length_ofFn] at key
  rw [values, key]
  -- the gate reads only vertices below `n + i`, which the prefix already holds
  exact DAGGate.eval_congr _ fun a ha =>
    runWith_getD_take _ _ _ hi.le (by simpa using C.args_lt i hi a ha) false

/-- Gate `i`'s depth is its gate's depth over the depths of all vertices. -/
theorem depthAt_gate {i : ℕ} (hi : i < C.gates.length) :
    C.depthAt (n + i) = C.gates[i].depth C.depths := by
  have key := runWith_getD_gate DAGGate.depth C.gates (List.replicate n 0) hi 0
  simp only [List.length_replicate] at key
  rw [depthAt, depths, key]
  exact DAGGate.depth_congr _ fun a ha =>
    runWith_getD_take _ _ _ hi.le (by simpa using C.args_lt i hi a ha) 0

end DAGCircuit

/-- The constant circuit on `n` inputs with output `b`: one constant gate
(`constGate b`), which is the output. -/
def constCircuit (n : ℕ) (b : Bool) : DAGCircuit n where
  gates := [constGate b]
  output := n
  args_lt := by intro i hi a ha; simp at hi; subst hi; simp at ha
  output_lt := by simp

/-- The constant circuit outputs its bit. -/
@[simp] theorem constCircuit_eval {n : ℕ} (b : Bool) (x : Fin n → Bool) :
    (constCircuit n b).eval x = b := by
  simp [DAGCircuit.eval, DAGCircuit.values, constCircuit, runWith_cons]

/-- The constant circuit has fan-in two. -/
theorem constCircuit_isFaninTwo (n : ℕ) (b : Bool) : (constCircuit n b).IsFaninTwo := by
  refine ⟨fun g hg => ?_, fun g hg => ?_⟩ <;>
    simp only [constCircuit, List.mem_singleton] at hg <;> subst hg <;>
    cases b <;> simp [constGate]

/-- The constant circuit has `n + 1` vertices. -/
@[simp] theorem constCircuit_size (n : ℕ) (b : Bool) : (constCircuit n b).size = n + 1 := rfl

/-! ## Circuit families -/

/-- A non-uniform family of circuits, one per input length. -/
structure DAGCircuitFamily where
  /-- The circuit handling inputs of length `n`. -/
  circuit : (n : ℕ) → DAGCircuit n

namespace DAGCircuitFamily

variable (C : DAGCircuitFamily)

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

/-- Every circuit of the family is well formed (unbounded fan-in, [AB09, Def 6.25]). -/
def IsWellFormed : Prop :=
  ∀ n, (C.circuit n).IsWellFormed

/-- Every circuit of the family has fan-in at most two ([AB09, Def 6.1]). -/
def HasFaninTwo : Prop :=
  ∀ n, (C.circuit n).IsFaninTwo

/-- The family has polynomial size.  [AB09] writes `|C_n| ≤ n ^ c`, which no family meets
(`Language.not_inSIZE_pow`, `PPoly.lean`: `n ^ c` is `0` at `n = 0` for `c ≥ 1`, and `1` at
`n = 2` for `c = 0`); `a * (n + 1) ^ k` repairs this, and differs from the literal bound only
at the lengths `n ≤ 1` (`Language.inPPoly_iff_eventually`). -/
def IsPolySize : Prop :=
  ∃ a k : ℕ, ∀ n, (C.circuit n).size ≤ a * (n + 1) ^ k

/-- The family has depth `O(log^d n)`; the `+ 1` keeps `n ≤ 1` from forcing depth `0`. -/
def HasPolylogDepth (d : ℕ) : Prop :=
  ∃ b : ℕ, ∀ n, (C.circuit n).depth ≤ b * (Nat.log 2 n + 1) ^ d

/-- A fan-in-two circuit family is in particular well formed: each of its circuits reads
distinct inputs at every gate and exactly one input at every `¬` gate. -/
theorem HasFaninTwo.isWellFormed {C : DAGCircuitFamily} (h : C.HasFaninTwo) :
    C.IsWellFormed :=
  fun n => (h n).1

end DAGCircuitFamily

end BoolCircuit
