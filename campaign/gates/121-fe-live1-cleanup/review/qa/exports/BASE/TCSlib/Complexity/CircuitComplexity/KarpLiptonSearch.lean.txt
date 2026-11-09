/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.PSubsetPPolyGadget

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Multi-output circuits and the search circuit of Karp–Lipton

[AB09, proof of Thm 6.19, p. 114]: from the circuits `C_n` deciding whether a partial
assignment extends to a satisfying one, "our algorithm of Theorem 2.18 converts any
decision algorithm for SAT into an algorithm that actually outputs a satisfying
assignment whenever one exists. Thinking of this algorithm as a circuit, we obtain from
the family `{C_n}` a `q(n)`-sized circuit family `{C'_n}` … such that … if there is a
string `v` such that `ϕ(u, v) = 1`, then `C'_n(ϕ, u)` outputs such a string `v`. (Note: We
did not formally define circuits with more than one bit of output, but it is an obvious
generalization of Definition 6.1.)"

This file makes both notions formal over the book's circuit model
`BoolCircuit.DAGCircuit`:

* a **multi-output circuit** is a DAG circuit with a list of output vertices
  (`BoolCircuit.MultiDAGCircuit`); each output alone is a Definition 6.1 circuit
  (`BoolCircuit.MultiDAGCircuit.outputCircuit`);
* the **search circuit** (`BoolCircuit.searchCircuit`), for an arbitrary relation `R`
  between inputs `y ∈ {0,1}ⁿ` and witnesses `v ∈ {0,1}ᵐ`: given circuits `D_j` (`1 ≤ j ≤ m`)
  on `n + j` inputs deciding whether a prefix `p ∈ {0,1}ʲ` extends to a witness, it
  chains copies of the `D_j` — the `j`-th copy reads `y`, the `j - 1` bits already output
  and a constant `1`, and outputs the next bit (the search of [AB09, Thm 2.18]: keep
  the bit `1` iff `p1` still extends). Whenever `y` has a witness, the outputs form one.

## Main definitions

* `BoolCircuit.MultiDAGCircuit` — circuits with several outputs, with `values`, `eval`,
  `size`, `IsFaninTwo` and `outputCircuit`.
* `BoolCircuit.searchBits` — the search procedure run on the decision circuits.
* `BoolCircuit.searchCircuit` — the search procedure as one multi-output circuit.

## Main results

* `BoolCircuit.MultiDAGCircuit.outputCircuit_eval` — output `i` alone is a single-output
  circuit computing bit `i`.
* `BoolCircuit.searchBits_spec` — the search finds a witness whenever one exists.
* `BoolCircuit.searchCircuit_eval`, `searchCircuit_isFaninTwo`, `searchCircuit_size_le`,
  `searchCircuit_correct` — the search circuit computes the search, has fan-in two and
  size at most `n + 1 + m (S + 1)` if every `D_j` has size at most `S` (so it is
  polynomial when `m` and `S` are), and outputs a witness whenever one exists.

## Divergences from [AB09]

* **General relation.** The book specializes to `ϕ(u, v) = 1` for a formula `ϕ`; we
  take any relation `R y v` and any decision circuits for its prefix-extension problem.
* **Size.** Each copy of `D_j` costs one extra copy gate, and one constant gate supplies
  the bit `1`; the book only says "`q(n)`-sized".
* **Use in the formal Karp–Lipton proof.** `KarpLipton.lean` does not evaluate this
  circuit; it checks the self-consistency of the decision circuits instead (see its
  module docstring). This file records the book's construction itself.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.5, Theorem 2.18; §6.1, Definition 6.1; §6.4,
  proof of Theorem 6.19, p. 114.)
-/

namespace BoolCircuit

/-! ### Multi-output circuits -/

/-- **A multi-output Boolean circuit** [AB09, p. 114: "the obvious generalization of
Definition 6.1"]: `n` input vertices, a gate list numbered topologically after them (as
in `BoolCircuit.DAGCircuit`), and a list of output vertices; the output is the string of
their values. -/
structure MultiDAGCircuit (n : ℕ) where
  /-- The gates, in topological order (gate `i` is vertex `n + i`). -/
  gates : List DAGGate
  /-- The output vertices, in order. -/
  outputs : List ℕ
  /-- Gate `i` reads only earlier vertices: the graph is acyclic. -/
  acyclic : GatesAcyclic n gates
  /-- Every output is a vertex of the circuit. -/
  outputs_lt : ∀ o ∈ outputs, o < n + gates.length

namespace MultiDAGCircuit

variable {n : ℕ} (C : MultiDAGCircuit n)

/-- The values of all vertices on input `x`: the inputs, then each gate in order. -/
def values (x : Fin n → Bool) : List Bool :=
  runWith DAGGate.eval C.gates (List.ofFn x)

/-- The output string of the circuit on input `x`: the values of the output vertices. -/
def eval (x : Fin n → Bool) : List Bool :=
  C.outputs.map fun o => (C.values x).getD o false

/-- The size: the number of vertices, inputs included ([AB09, Def 6.1]). -/
def size : ℕ := n + C.gates.length

/-- Well formed with fan-in at most two, as in `BoolCircuit.DAGCircuit.IsFaninTwo`. -/
def IsFaninTwo : Prop :=
  (∀ g ∈ C.gates, g.args.Nodup ∧ (g.kind = .not → g.args.length = 1)) ∧
    ∀ g ∈ C.gates, g.args.length ≤ 2

/-- The output string has one bit per output vertex. -/
@[simp] theorem length_eval (x : Fin n → Bool) : (C.eval x).length = C.outputs.length := by
  simp [eval]

/-- **Output `i` as a single-output circuit** ([AB09, Def 6.1]): the same gates with the
`i`-th output vertex as the output. -/
def outputCircuit (i : ℕ) (hi : i < C.outputs.length) : DAGCircuit n where
  gates := C.gates
  output := C.outputs[i]
  args_lt := C.acyclic
  output_lt := C.outputs_lt _ (List.getElem_mem hi)

/-- The `i`-th single-output circuit computes the `i`-th output bit. -/
theorem outputCircuit_eval (i : ℕ) (hi : i < C.outputs.length) (x : Fin n → Bool) :
    (C.outputCircuit i hi).eval x = (C.eval x)[i]'(by simpa using hi) := by
  simp [outputCircuit, eval, DAGCircuit.eval, DAGCircuit.values, values]

/-- Each output circuit of a fan-in-two multi-output circuit has fan-in two. -/
theorem outputCircuit_isFaninTwo (h : C.IsFaninTwo) (i : ℕ) (hi : i < C.outputs.length) :
    (C.outputCircuit i hi).IsFaninTwo :=
  ⟨h.1, h.2⟩

end MultiDAGCircuit

/-! ### The search procedure -/

section Search

variable {n : ℕ} (D : (j : ℕ) → DAGCircuit (n + j))

/-- A partial witness `p` **extends** to a witness of length `m` for `y` under `R`. -/
def Extends (R : List Bool → List Bool → Prop) (m : ℕ) (y p : List Bool) : Prop :=
  ∃ s : List Bool, (p ++ s).length = m ∧ R y (p ++ s)

/-- **The search of [AB09, Thm 2.18] run on decision circuits**: after the bits `p`
found so far, the next bit is the answer of `D_{|p|+1}` on `(y, p 1)`. -/
def searchBits (y : List Bool) : ℕ → List Bool
  | 0 => []
  | j + 1 => searchBits y j ++
      [(D (j + 1)).eval fun i => (y ++ (searchBits y j ++ [true])).getD i false]

/-- The search outputs one bit per stage. -/
@[simp] theorem length_searchBits (y : List Bool) (j : ℕ) : (searchBits D y j).length = j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [searchBits, ih]

/-- **The search finds a witness** [AB09, Thm 2.18, as used on p. 114]: if each `D_j`
(`1 ≤ j ≤ m`) decides whether a length-`j` prefix extends to a witness for `y`, and `y`
has a witness of length `m`, then the search output of length `m` is a witness.

**Proof sketch.** Induction on `j ≤ m`: the prefix found after `j` steps extends. If
`D_{j+1}` accepts `p 1`, then `p 1` extends; otherwise `p 1` does not extend, and since
`p` extends by some nonempty `b s`, necessarily `b = 0`, so `p 0` extends. At `j = m`
the extension is empty. -/
theorem searchBits_spec (R : List Bool → List Bool → Prop) (m : ℕ)
    (hD : ∀ j, 1 ≤ j → j ≤ m → ∀ y p : List Bool, y.length = n → p.length = j →
      ((D j).eval (fun i => (y ++ p).getD i false) = true ↔ Extends R m y p))
    (y : List Bool) (hy : y.length = n) (hex : ∃ v, v.length = m ∧ R y v) :
    R y (searchBits D y m) := by
  have step : ∀ j, j ≤ m → Extends R m y (searchBits D y j) := by
    intro j
    induction j with
    | zero => intro _; obtain ⟨v, hv, hR⟩ := hex; exact ⟨v, by simpa using hv, by simpa using hR⟩
    | succ j ih =>
      intro hj
      obtain ⟨s, hs, hR⟩ := ih (by omega)
      have hq := hD (j + 1) (by omega) hj y (searchBits D y j ++ [true]) hy (by simp)
      simp only [searchBits]
      cases hb : (D (j + 1)).eval fun i => (y ++ (searchBits D y j ++ [true])).getD i false
      · -- the bit `1` does not extend, so the extension starts with `0`
        have hno : ¬ Extends R m y (searchBits D y j ++ [true]) := by
          rw [← hq, hb]; simp
        obtain ⟨b, s', rfl⟩ : ∃ b s', s = b :: s' := by
          cases s with
          | nil => simp at hs; omega
          | cons b s' => exact ⟨b, s', rfl⟩
        cases b
        · exact ⟨s', by simpa using hs, by simpa using hR⟩
        · exact absurd ⟨s', by simpa using hs, by simpa using hR⟩ hno
      · exact hq.mp hb
  obtain ⟨s, hs, hR⟩ := step m le_rfl
  rw [List.length_append, length_searchBits] at hs
  have : s = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst this
  simpa using hR

/-! ### The search circuit -/

/-- One stage of the search circuit: append a copy of `D_{j+1}` reading the `n` inputs,
the output vertices `outs` found so far and the constant vertex `n`, and record its
output vertex. -/
def searchStep (j : ℕ) (s : List DAGGate × List ℕ) : List DAGGate × List ℕ :=
  (s.1 ++ embedGates (D (j + 1)) (List.range n ++ s.2 ++ [n]) (n + s.1.length),
    s.2 ++ [n + s.1.length + (D (j + 1)).gates.length])

/-- The gates and output vertices of the search circuit after `j` stages; stage `0` is
the constant-`1` gate at vertex `n`. -/
def searchState : ℕ → List DAGGate × List ℕ
  | 0 => ([constGate true], [])
  | j + 1 => searchStep D j (searchState j)

/-- The number of gates after `j` stages is at most `1 + j (S + 1)` when every `D_j` has
size at most `S` (`1 ≤ j ≤ M`, `j` stages with `j ≤ M`): one constant gate plus, per stage, the gates of the copy and one copy
gate. -/
theorem length_searchState_le (S M : ℕ) (hS : ∀ j, 1 ≤ j → j ≤ M → (D j).size ≤ S)
    (j : ℕ) (hj : j ≤ M) : (searchState D j).1.length ≤ 1 + j * (S + 1) := by
  induction j with
  | zero => simp [searchState]
  | succ j ih =>
    have ih := ih (by omega)
    have h := hS (j + 1) (by omega) hj
    simp only [DAGCircuit.size] at h
    simp only [searchState, searchStep, List.length_append, length_embedGates]
    rw [Nat.succ_mul]
    omega

/-- Structural invariant of the search circuit: acyclic, `j` outputs, all outputs and
the constant vertex are existing vertices, and every gate is well formed of fan-in at
most two (when the `D_j` are).

**Proof sketch.** Induction on `j`. Stage `0` is the single constant gate. A stage
appends a copy of `D_{j+1}` whose sources (the inputs, the outputs so far and the
constant vertex `n`) are existing vertices, so the copy reads only earlier vertices
(`gatesAcyclic_embedGates`) and keeps fan-in two (`faninTwo_embedGates`); its output
vertex, the copy gate, is the last new vertex. -/
theorem searchState_struct (hD : ∀ j, (D j).IsFaninTwo) (j : ℕ) :
    GatesAcyclic n (searchState D j).1 ∧ (searchState D j).2.length = j ∧
      (∀ o ∈ (searchState D j).2, o < n + (searchState D j).1.length) ∧
      n < n + (searchState D j).1.length ∧
      ∀ g ∈ (searchState D j).1,
        g.args.Nodup ∧ (g.kind = .not → g.args.length = 1) ∧ g.args.length ≤ 2 := by
  induction j with
  | zero =>
    refine ⟨GatesAcyclic.nil.snoc (by simp), rfl, by simp [searchState], by simp [searchState],
      ?_⟩
    intro g hg
    simp only [searchState, List.mem_singleton] at hg
    subst hg
    simp [constGate]
  | succ j ih =>
    rw [show searchState D (j + 1) = searchStep D j (searchState D j) from rfl]
    generalize searchState D j = s at ih ⊢
    obtain ⟨hac, hlen, hout, hn, hfan⟩ := ih
    have hsrc : ∀ a ∈ List.range n ++ s.2 ++ [n], a < n + s.1.length := by
      intro a ha
      simp only [List.mem_append, List.mem_range, List.mem_singleton] at ha
      rcases ha with (ha | ha) | rfl
      · omega
      · exact hout a ha
      · exact hn
    have hsl : (List.range n ++ s.2 ++ [n]).length = n + (j + 1) := by simp [hlen]
    simp only [searchStep]
    refine ⟨hac.append (gatesAcyclic_embedGates _ _ _ hsl hsrc), by simp [hlen], ?_, ?_, ?_⟩
    · intro o ho
      simp only [List.mem_append, List.mem_singleton] at ho
      simp only [List.length_append, length_embedGates]
      rcases ho with ho | rfl
      · have := hout o ho; omega
      · omega
    · simp only [List.length_append]; omega
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hfan g hg
      · exact faninTwo_embedGates _ (hD _) _ _ g hg

/-- Semantic invariant of the search circuit: on input `x`, the constant vertex holds `1`
and the output vertices hold the search bits.

**Proof sketch.** Induction on `j`. Appending gates never changes existing vertices
(`runWith_getD_of_lt`), so the constant and the old outputs keep their values. The
sources of the new copy of `D_{j+1}` read, in order, the input `x`, the bits found so far
and the constant `1`, so its output vertex holds `D_{j+1}(x, p 1)`
(`runWith_embedGates_getD`), which is the next search bit. -/
theorem searchState_values (hD : ∀ j, (D j).IsFaninTwo) (x : Fin n → Bool) (j : ℕ) :
    (runWith DAGGate.eval (searchState D j).1 (List.ofFn x)).getD n false = true ∧
      (searchState D j).2.map
          (fun o => (runWith DAGGate.eval (searchState D j).1 (List.ofFn x)).getD o false) =
        searchBits D (List.ofFn x) j := by
  induction j with
  | zero =>
    refine ⟨?_, rfl⟩
    simp only [searchState, runWith_singleton]
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  | succ j ih =>
    obtain ⟨-, hlen, hout, hn, -⟩ := searchState_struct D hD j
    rw [show searchState D (j + 1) = searchStep D j (searchState D j) from rfl]
    generalize searchState D j = s at ih hlen hout hn ⊢
    obtain ⟨hc, hb⟩ := ih
    set vals := runWith DAGGate.eval s.1 (List.ofFn x) with hvals
    have hL : vals.length = n + s.1.length := by simp [hvals]
    set srcs := List.range n ++ s.2 ++ [n] with hsrcs
    have hsrc : ∀ a ∈ srcs, a < vals.length := by
      intro a ha
      simp only [hsrcs, List.mem_append, List.mem_range, List.mem_singleton] at ha
      rcases ha with (ha | ha) | rfl
      · omega
      · have := hout a ha; omega
      · omega
    have hsl : srcs.length = n + (j + 1) := by simp [hsrcs, hlen]
    -- the old vertices keep their values
    have hold : ∀ v, v < vals.length →
        (runWith DAGGate.eval (s.1 ++ embedGates (D (j + 1)) srcs (n + s.1.length))
          (List.ofFn x)).getD v false = vals.getD v false := by
      intro v hv
      rw [runWith_append, runWith_getD_of_lt _ _ _ hv]
    -- the sources carry the input, the bits found so far and the constant `1`
    have hmap : srcs.map (fun o => vals.getD o false) =
        List.ofFn x ++ (searchBits D (List.ofFn x) j ++ [true]) := by
      have hin : (List.range n).map (fun o => vals.getD o false) = List.ofFn x := by
        apply List.ext_getElem (by simp)
        intro i h1 h2
        simp only [List.getElem_map, List.getElem_range, hvals]
        have hi : i < n := by simpa using h2
        rw [runWith_getD_of_lt _ _ _ (by simpa using h2)]
        simp [hi]
      simp only [hsrcs, List.map_append, hin, hb, List.map_cons, List.map_nil, hc,
        List.append_assoc]
    -- the new output vertex holds the next search bit
    have hnew : (runWith DAGGate.eval (s.1 ++ embedGates (D (j + 1)) srcs (n + s.1.length))
          (List.ofFn x)).getD (n + s.1.length + (D (j + 1)).gates.length) false =
        (D (j + 1)).eval fun i =>
          (List.ofFn x ++ (searchBits D (List.ofFn x) j ++ [true])).getD i false := by
      rw [runWith_append, ← hvals, ← hL, runWith_embedGates_getD _ _ hsl _ hsrc]
      congr 1
      funext i
      have h := getD_map_getD (l := srcs) (f := fun o => vals.getD o false) (i := i)
        (by rw [hsl]; exact i.isLt)
      simp only at h
      rw [h, hmap]
    simp only [searchStep]
    refine ⟨by rw [hold n (by omega)]; exact hc, ?_⟩
    rw [List.map_append, List.map_singleton, hnew, searchBits]
    congr 1
    rw [← hb]
    refine List.map_congr_left fun o ho => ?_
    exact hold o (by have := hout o ho; omega)

/-- **The search circuit** [AB09, p. 114, the circuit `C'_n`]: the `m`-stage search over
the decision circuits `D_1, …, D_m`, as one multi-output circuit on `n` inputs with `m`
outputs. -/
def searchCircuit (hD : ∀ j, (D j).IsFaninTwo) (m : ℕ) : MultiDAGCircuit n where
  gates := (searchState D m).1
  outputs := (searchState D m).2
  acyclic := (searchState_struct D hD m).1
  outputs_lt := (searchState_struct D hD m).2.2.1

/-- The search circuit outputs the search bits. -/
theorem searchCircuit_eval (hD : ∀ j, (D j).IsFaninTwo) (m : ℕ) (x : Fin n → Bool) :
    (searchCircuit D hD m).eval x = searchBits D (List.ofFn x) m :=
  (searchState_values D hD x m).2

/-- The search circuit has fan-in two. -/
theorem searchCircuit_isFaninTwo (hD : ∀ j, (D j).IsFaninTwo) (m : ℕ) :
    (searchCircuit D hD m).IsFaninTwo := by
  have h := (searchState_struct D hD m).2.2.2.2
  exact ⟨fun g hg => ⟨(h g hg).1, (h g hg).2.1⟩, fun g hg => (h g hg).2.2⟩

/-- **The search circuit has polynomial size** [AB09, p. 114: "a `q(n)`-sized circuit
family"]: if every used `D_j` (`1 ≤ j ≤ m`) has size at most `S`, the search circuit
has size at most `n + 1 + m (S + 1)`. -/
theorem searchCircuit_size_le (hD : ∀ j, (D j).IsFaninTwo) (m S : ℕ)
    (hS : ∀ j, 1 ≤ j → j ≤ m → (D j).size ≤ S) :
    (searchCircuit D hD m).size ≤ n + 1 + m * (S + 1) := by
  have := length_searchState_le D S m hS m le_rfl
  simp only [MultiDAGCircuit.size, searchCircuit]
  omega

/-- **The search circuit outputs a witness** [AB09, p. 114: "if there is a string `v` such
that `ϕ(u, v) = 1`, then `C'_n(ϕ, u)` outputs such a string `v`"], for an arbitrary
relation `R` in place of `ϕ(u, v) = 1`: if each `D_j` decides the prefix-extension
problem of `R` for length-`j` prefixes, then on every input with a witness of length `m`
the circuit's `m`-bit output is a witness. -/
theorem searchCircuit_correct (hD : ∀ j, (D j).IsFaninTwo) (R : List Bool → List Bool → Prop)
    (m : ℕ) (hdec : ∀ j, 1 ≤ j → j ≤ m → ∀ y p : List Bool, y.length = n → p.length = j →
      ((D j).eval (fun i => (y ++ p).getD i false) = true ↔ Extends R m y p))
    (x : Fin n → Bool) (hex : ∃ v, v.length = m ∧ R (List.ofFn x) v) :
    ((searchCircuit D hD m).eval x).length = m ∧ R (List.ofFn x) ((searchCircuit D hD m).eval x) := by
  rw [searchCircuit_eval]
  exact ⟨length_searchBits D _ m, searchBits_spec D R m hdec _ (by simp) hex⟩

end Search

end BoolCircuit
