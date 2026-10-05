/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Computability.Language
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Log

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

## Main results

* `BoolCircuit.runWith_getD_gate` — the value (or depth) of gate `i` is computed from the
  vertices before it; `BoolCircuit.runWith_getD_of_lt` — appending gates never changes
  the value of an existing vertex.  These two facts drive every proof about the model.
* `BoolCircuit.DAGCircuit.eval_gate`, `BoolCircuit.DAGCircuit.depthAt_gate` — the
  evaluation and depth recurrences at a gate vertex.

## Divergences from [AB09, Def 6.1]

* **`∧`/`∨` fan-in is at most two, not exactly two.**  [AB09] gives every `∧`/`∨` gate
  fan-in `2` and has no constants.  Taken literally, a circuit on `0` inputs has no
  vertex to output, so no language would be decidable at length `0`; allowing fan-in `0`
  gives the constants (`∧` of nothing is `true`, `∨` of nothing is `false`), and fan-in `1`
  is an identity gate that can always be bypassed.
* **Single output.**  [AB09, Def 6.1] allows `m` outputs; deciding a language needs one,
  and every class in the book uses one.
* **Unused gates.**  Gates from which no path reaches the output
  are allowed and counted in `size`, as in [AB09] (whose size counts every
  vertex).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, Definitions 6.1 and 6.2.)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

/-- The label of a gate: `∧`, `∨` or `¬`.  [AB09, Def 6.1] -/
inductive GateKind where
  | and
  | or
  | not
  deriving DecidableEq, Repr

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

@[simp] theorem runWith_nil (init : List β) : runWith f [] init = init := rfl

theorem runWith_cons (g : DAGGate) (gs : List DAGGate) (init : List β) :
    runWith f (g :: gs) init = runWith f gs (init ++ [f g init]) := rfl

theorem runWith_append (gs hs : List DAGGate) (init : List β) :
    runWith f (gs ++ hs) init = runWith f hs (runWith f gs init) := by
  simp [runWith, List.foldl_append]

theorem runWith_singleton (g : DAGGate) (init : List β) :
    runWith f [g] init = init ++ [f g init] := rfl

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

private theorem all_congr_mem {l : List ℕ} {p q : ℕ → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, h a (by simp), ih (fun b hb => h b (by simp [hb]))]

private theorem any_congr_mem {l : List ℕ} {p q : ℕ → Bool} (h : ∀ a ∈ l, p a = q a) :
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

@[simp] theorem length_values (x : Fin n → Bool) :
    (C.values x).length = n + C.gates.length := by
  simp [values]

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

/-- The family has polynomial size.  [AB09] writes `|C_n| ≤ n ^ c`; `a * (n + 1) ^ k`
repairs the degeneracy at `n = 0`, where `n ^ c` would force size `0`. -/
def IsPolySize : Prop :=
  ∃ a k : ℕ, ∀ n, (C.circuit n).size ≤ a * (n + 1) ^ k

/-- The family has depth `O(log^d n)`; the `+ 1` keeps `n ≤ 1` from forcing depth `0`. -/
def HasPolylogDepth (d : ℕ) : Prop :=
  ∃ b : ℕ, ∀ n, (C.circuit n).depth ≤ b * (Nat.log 2 n + 1) ^ d

theorem HasFaninTwo.isWellFormed {C : DAGCircuitFamily} (h : C.HasFaninTwo) :
    C.IsWellFormed :=
  fun n => (h n).1

end DAGCircuitFamily

end BoolCircuit
