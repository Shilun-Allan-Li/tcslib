/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.StrictCircuit
import TCSlib.Complexity.CircuitComplexity.PPoly

/-!
# Strictification and the strict size classes

Every fan-in-two circuit (`BoolCircuit.DAGCircuit.IsFaninTwo`) with at least one input is
equivalent to a circuit of the literal model of [AB09, Def 6.1]
(`BoolCircuit.DAGCircuit.IsStrict`, `StrictCircuit.lean`) of at most four times the size
plus `12`.  Consequently `SIZE` and `P/poly` do not depend on the relaxation, up to that
constant factor.

## Main definitions

* `BoolCircuit.sealGates`, `BoolCircuit.DAGCircuit.seal` — attach every dead vertex `u`
  (a sink other than the output) by `o ↦ o ∧ (u ∨ ¬u)`.
* `BoolCircuit.DAGCircuit.strictify` — `seal ∘ deconst`; `BoolCircuit.DAGCircuitFamily.strictify`.
* `Language.InStrictSIZE`, `Language.InStrictPPoly` — `SIZE` and `P/poly` over strict
  circuits at every input length `n ≥ 1`.

## Main results

* `BoolCircuit.DAGCircuit.seal_isStrict`, `seal_hasFanoutTwo`, `seal_size_le` — sealing.
* `BoolCircuit.DAGCircuit.exists_isStrict` — for `n ≥ 1`, every fan-in-two circuit of size
  `S` has an equivalent strict circuit of size at most `4S + 12`.
* `Language.InSIZE.inStrictSIZE`, `Language.InStrictSIZE.inSIZE`,
  `Language.inPPoly_iff_inStrictPPoly` — the size classes transfer.

## Divergences from [AB09, Defs 6.1, 6.2, 6.5]

* **Length `0`.**  No strict circuit has `0` inputs
  (`BoolCircuit.DAGCircuit.not_isStrict_zero`), so the strict classes allow any fan-in-two
  circuit at `n = 0`.  Taken literally, `SIZE(T)` and `P/poly` would be empty, since no
  family has a length-`0` member.
* **Unused inputs.**  Def 6.1 has exactly one sink, so a strict circuit reads every input,
  even for a function that ignores it.  Sealing reads such inputs harmlessly.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, Definitions 6.1, 6.2 and 6.5.)
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

variable {n : ℕ}

/-! ## Attaching dead vertices to the output -/

/-- The three gates attaching the vertex `u` to the current output `o`, appended at vertex
`N`: `¬u` (vertex `N`), `u ∨ ¬u = 1` (vertex `N + 1`) and the new output `o ∧ 1`
(vertex `N + 2`). -/
def sealTriple (u N o : ℕ) : List DAGGate :=
  [⟨.not, [u]⟩, ⟨.or, [u, N]⟩, ⟨.and, [o, N + 1]⟩]

/-- One sealing step: attach `u` to the current output, which moves to the new last
vertex. -/
def sealStep (n : ℕ) (s : List DAGGate × ℕ) (u : ℕ) : List DAGGate × ℕ :=
  (s.1 ++ sealTriple u (n + s.1.length) s.2, n + s.1.length + 2)

/-- Attach every vertex of `L`, in order, to the output. -/
def sealGates (n : ℕ) (L : List ℕ) (s : List DAGGate × ℕ) : List DAGGate × ℕ :=
  L.foldl (sealStep n) s

/-- The fan-out the triple adds: `u` is read twice, `N`, `o` and `N + 1` once each. -/
theorem fanoutIn_sealTriple {u N o : ℕ} (hu : u < N) (ho : o < N) (v : ℕ) :
    fanoutIn (sealTriple u N o) v =
      (if v = u then 2 else 0) + (if v = N then 1 else 0) + (if v = o then 1 else 0) +
        (if v = N + 1 then 1 else 0) := by
  simp only [fanoutIn, sealTriple, List.countP_cons, List.countP_nil, List.mem_cons,
    List.not_mem_nil, or_false, decide_eq_true_eq]
  split_ifs <;> omega

/-- The triple's gates are strict. -/
theorem sealTriple_strict {u N o : ℕ} (hu : u < N) (ho : o < N) :
    ∀ g ∈ sealTriple u N o, g.Strict := by
  intro g hg
  simp only [sealTriple, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simp [DAGGate.Strict] <;> omega

/-- The triple reads only vertices before each of its gates. -/
theorem sealTriple_acyclic {u N o : ℕ} (hu : u < N) (ho : o < N) :
    GatesAcyclic N (sealTriple u N o) := by
  simp only [sealTriple, gatesAcyclic_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, gatesAcyclic_nil, and_true]
  omega

/-- The new output of a sealing step computes the old output: `o ∧ (u ∨ ¬u) = o`.

**Proof sketch.** Split the three appended gates off one at a time.  The last gate is
`o ∧ (vertex N + 1)`; appending gates leaves the value of the old vertex `o` unchanged.
Vertex `N + 1` is `u ∨ (vertex N)` and vertex `N` is `¬u`, so it holds `u ∨ ¬u = 1`, and
`o ∧ 1 = o`. -/
theorem vertexValue_sealStep (gs : List DAGGate) (x : Fin n → Bool) {u o : ℕ}
    (hu : u < n + gs.length) (ho : o < n + gs.length) :
    vertexValue (sealStep n (gs, o) u).1 x (sealStep n (gs, o) u).2 = vertexValue gs x o := by
  have hsplit : gs ++ sealTriple u (n + gs.length) o =
      gs ++ [⟨.not, [u]⟩] ++ [⟨.or, [u, n + gs.length]⟩] ++ [⟨.and, [o, n + gs.length + 1]⟩] := by
    simp [sealTriple]
  simp only [sealStep]
  rw [hsplit]
  have hN2 : n + gs.length + 2 = n + (gs ++ [(⟨.not, [u]⟩ : DAGGate)] ++
      [(⟨.or, [u, n + gs.length]⟩ : DAGGate)]).length := by
    simp; omega
  have hN1 : n + gs.length + 1 = n + (gs ++ [(⟨.not, [u]⟩ : DAGGate)]).length := by
    simp; omega
  rw [hN2, vertexValue_last, DAGGate.eval_pair (by decide)]
  change (vertexValue _ x o && vertexValue _ x (n + gs.length + 1)) = _
  rw [List.append_assoc, vertexValue_append _ _ _ ho, ← List.append_assoc, hN1, vertexValue_last,
    DAGGate.eval_pair (by decide)]
  change (_ && (vertexValue _ x u || vertexValue _ x (n + gs.length))) = _
  rw [vertexValue_append _ _ _ hu, vertexValue_last]
  simp only [DAGGate.eval, List.all_cons, List.all_nil, Bool.and_true]
  change (_ && (_ || !vertexValue gs x u)) = _
  cases vertexValue gs x u <;> simp

/-- What sealing guarantees: it only appends strict gates, stays acyclic, and its output
computes the old output. -/
structure SealSpec (n : ℕ) (gs : List DAGGate) (o : ℕ) (r : List DAGGate × ℕ) : Prop where
  extends_gates : ∃ ext, r.1 = gs ++ ext ∧ ∀ g ∈ ext, g.Strict
  acyclic : GatesAcyclic n r.1
  output_lt : r.2 < n + r.1.length
  value : ∀ x : Fin n → Bool, vertexValue r.1 x r.2 = vertexValue gs x o

/-- Sealing appends exactly three gates per attached vertex. -/
theorem sealGates_length (L : List ℕ) (s : List DAGGate × ℕ) :
    (sealGates n L s).1.length = s.1.length + 3 * L.length := by
  induction L generalizing s with
  | nil => simp [sealGates]
  | cons u L ih =>
    rw [sealGates, List.foldl_cons, ← sealGates, ih]
    simp [sealStep, sealTriple]; omega

/-- Sealing meets `SealSpec` when the attached vertices and the output exist.

**Proof sketch.** Induction on the list `L` of attached vertices, generalizing the gate
list and the current output.  One step appends the triple `¬u`, `u ∨ ¬u`, `o ∧ (u ∨ ¬u)`.
Its gates are strict (`u` and `o` lie below the new vertex `N`) and read only earlier
vertices.  The new output `N + 2` exists and computes the old output
(`vertexValue_sealStep`).  The remaining vertices of `L` still exist after the step, so
the induction hypothesis applies; the strict extensions and the value equalities compose. -/
theorem sealGates_spec : ∀ (L : List ℕ) (gs : List DAGGate) (o : ℕ), GatesAcyclic n gs →
    o < n + gs.length → (∀ u ∈ L, u < n + gs.length) → SealSpec n gs o (sealGates n L (gs, o))
  | [], gs, o, hgs, ho, _ => ⟨⟨[], by simp [sealGates], by simp⟩, hgs, ho, fun _ => rfl⟩
  | u :: L, gs, o, hgs, ho, hL => by
    have hu := hL u (by simp)
    set N := n + gs.length with hN
    have hstep : sealStep n (gs, o) u = (gs ++ sealTriple u N o, N + 2) := rfl
    have hac : GatesAcyclic n (gs ++ sealTriple u N o) :=
      gatesAcyclic_append.mpr ⟨hgs, sealTriple_acyclic hu ho⟩
    have hlen : (gs ++ sealTriple u N o).length = gs.length + 3 := by simp [sealTriple]
    have ih := sealGates_spec L (gs ++ sealTriple u N o) (N + 2) hac (by rw [hlen]; omega)
      fun v hv => by have := hL v (by simp [hv]); rw [hlen]; omega
    have hres : sealGates n (u :: L) (gs, o) = sealGates n L (gs ++ sealTriple u N o, N + 2) :=
      by rw [sealGates, List.foldl_cons, hstep]; rfl
    rw [hres]
    obtain ⟨ext, hext, hstrict⟩ := ih.extends_gates
    refine ⟨⟨sealTriple u N o ++ ext, by rw [hext, List.append_assoc], fun g hg => ?_⟩,
      ih.acyclic, ih.output_lt, fun x => ?_⟩
    · rcases List.mem_append.mp hg with hg | hg
      · exact sealTriple_strict hu ho g hg
      · exact hstrict g hg
    · rw [ih.value x]
      exact vertexValue_sealStep gs x hu ho

/-- After sealing, every vertex except the new output is read, provided every old vertex
other than the old output and the attached vertices was already read.

**Proof sketch.** Induction on `L`.  After the step for `u`, check the hypothesis for the
new state, i.e. every vertex below `N + 3` other than the new output `N + 2` and the rest
of `L` is read.  The old output `o` is read by `o ∧ (u ∨ ¬u)`, `u` by `¬u` and `u ∨ ¬u`,
`N = ¬u` by `u ∨ ¬u`, and `N + 1` by the new output.  Every other old vertex was read
before, and appending gates only adds readers.  With `L` empty the hypothesis is the
claim. -/
theorem sealGates_read : ∀ (L : List ℕ) (gs : List DAGGate) (o : ℕ),
    o < n + gs.length → (∀ u ∈ L, u < n + gs.length) →
    (∀ v < n + gs.length, v ≠ o → v ∉ L → 0 < fanoutIn gs v) →
    ∀ v < n + (sealGates n L (gs, o)).1.length, v ≠ (sealGates n L (gs, o)).2 →
      0 < fanoutIn (sealGates n L (gs, o)).1 v
  | [], gs, o, _, _, hread => fun v hv hne => hread v hv hne (by simp)
  | u :: L, gs, o, ho, hL, hread => by
    have hu := hL u (by simp)
    set N := n + gs.length with hN
    have hlen : (gs ++ sealTriple u N o).length = gs.length + 3 := by simp [sealTriple]
    have hres : sealGates n (u :: L) (gs, o) = sealGates n L (gs ++ sealTriple u N o, N + 2) :=
      rfl
    rw [hres]
    refine sealGates_read L _ _ (by rw [hlen]; omega)
      (fun v hv => by have := hL v (by simp [hv]); rw [hlen]; omega) fun v hv hne hvL => ?_
    rw [fanoutIn_append, fanoutIn_sealTriple hu ho]
    rw [hlen] at hv
    by_cases hvN : v < N
    · by_cases hvo : v = o
      · subst hvo; split_ifs <;> omega
      by_cases hvu : v = u
      · subst hvu; split_ifs <;> omega
      have := hread v hvN hvo (by simp [hvu, hvL])
      omega
    · split_ifs <;> omega

/-- Sealing keeps fan-out at most two, when the attached vertices are distinct, unread
and not the output, and the output is read at most once.

**Proof sketch.** Induction on `L` (which has no duplicates and does not contain `o`).  One
step reads the dead vertex `u` twice (it was unread), the fresh vertex `¬u` once, the
current output `o` once (read at most once before, never again afterwards), and the fresh
vertex `u ∨ ¬u` once; every other vertex keeps its fan-out.  The invariants pass to the
new state.  The new output `N + 2` is unread.  The remaining vertices of `L` are distinct
from `u` (no duplicates), from `o` and from the fresh vertices, so they are still
unread. -/
theorem sealGates_fanout : ∀ (L : List ℕ) (gs : List DAGGate) (o : ℕ), GatesAcyclic n gs →
    o < n + gs.length → (∀ u ∈ L, u < n + gs.length) → L.Nodup → o ∉ L →
    (∀ u ∈ L, fanoutIn gs u = 0) → fanoutIn gs o ≤ 1 → (∀ v, fanoutIn gs v ≤ 2) →
    ∀ v, fanoutIn (sealGates n L (gs, o)).1 v ≤ 2
  | [], gs, _, _, _, _, _, _, _, _, hle => hle
  | u :: L, gs, o, hgs, ho, hL, hnd, hoL, hzero, hone, hle => by
    have hu := hL u (by simp)
    set N := n + gs.length with hN
    have hlen : (gs ++ sealTriple u N o).length = gs.length + 3 := by simp [sealTriple]
    have hres : sealGates n (u :: L) (gs, o) = sealGates n L (gs ++ sealTriple u N o, N + 2) :=
      rfl
    rw [hres]
    have hgeN : ∀ v, N ≤ v → fanoutIn gs v = 0 := fun v hv => fanoutIn_eq_zero_of_le hgs hv
    have hLlt : ∀ v ∈ L, v < N := fun v hv => hL v (by simp [hv])
    have hnd' := List.nodup_cons.mp hnd
    refine sealGates_fanout L _ _ (gatesAcyclic_append.mpr ⟨hgs, sealTriple_acyclic hu ho⟩)
      (by rw [hlen]; omega) (fun v hv => by have := hLlt v hv; rw [hlen]; omega) hnd'.2
      (fun h => by have := hLlt _ h; omega) (fun v hv => ?_) ?_ fun v => ?_
    · rw [fanoutIn_append, fanoutIn_sealTriple hu ho, hzero v (by simp [hv])]
      have := hLlt v hv
      have hvu : v ≠ u := fun h => hnd'.1 (h ▸ hv)
      have hvo : v ≠ o := fun h => hoL (by simp [← h, hv])
      split_ifs <;> omega
    · rw [fanoutIn_append, fanoutIn_sealTriple hu ho, hgeN _ (by omega)]
      split_ifs <;> omega
    · rw [fanoutIn_append, fanoutIn_sealTriple hu ho]
      have h1 := hle v
      by_cases hvu : v = u
      · subst hvu
        have := hzero v (by simp)
        have hvo : v ≠ o := fun h => hoL (by simp [h])
        split_ifs <;> omega
      by_cases hvo : v = o
      · subst hvo; split_ifs <;> omega
      by_cases hvN : v < N
      · split_ifs <;> omega
      · have := hgeN v (by omega); split_ifs <;> omega

/-! ## Sealing a circuit -/

/-- The dead vertices of a circuit: those other than the output that no gate reads (the
sinks other than the output). -/
def DAGCircuit.deadVertices (C : DAGCircuit n) : List ℕ :=
  (List.range C.size).filter fun v => v ≠ C.output ∧ C.fanout v = 0

/-- `v` is dead iff it is a vertex other than the output with fan-out `0`. -/
theorem DAGCircuit.mem_deadVertices {C : DAGCircuit n} {v : ℕ} :
    v ∈ C.deadVertices ↔ v < C.size ∧ v ≠ C.output ∧ C.fanout v = 0 := by
  simp [DAGCircuit.deadVertices]

/-- The circuit `C` with every dead vertex `u` attached to the output by the gadget
`o ↦ o ∧ (u ∨ ¬u)`, so that the output becomes the only sink. -/
def DAGCircuit.seal (C : DAGCircuit n) : DAGCircuit n where
  gates := (sealGates n C.deadVertices (C.gates, C.output)).1
  output := (sealGates n C.deadVertices (C.gates, C.output)).2
  args_lt := (sealGates_spec C.deadVertices C.gates C.output C.args_lt C.output_lt
    fun _ hu => (DAGCircuit.mem_deadVertices.mp hu).1).acyclic
  output_lt := (sealGates_spec C.deadVertices C.gates C.output C.args_lt C.output_lt
    fun _ hu => (DAGCircuit.mem_deadVertices.mp hu).1).output_lt

section Seal

variable (C : DAGCircuit n)

private theorem seal_spec : SealSpec n C.gates C.output
    (sealGates n C.deadVertices (C.gates, C.output)) :=
  sealGates_spec C.deadVertices C.gates C.output C.args_lt C.output_lt
    fun _ hu => (DAGCircuit.mem_deadVertices.mp hu).1

/-- Sealing preserves the function computed. -/
theorem DAGCircuit.seal_eval (x : Fin n → Bool) : C.seal.eval x = C.eval x :=
  (seal_spec C).value x

/-- Sealing at most quadruples the size: three gates per dead vertex. -/
theorem DAGCircuit.seal_size_le : C.seal.size ≤ 4 * C.size := by
  have h := sealGates_length (n := n) C.deadVertices (C.gates, C.output)
  have hd : C.deadVertices.length ≤ C.size := by
    have := List.length_filter_le (fun v => decide (v ≠ C.output ∧ C.fanout v = 0))
      (List.range C.size)
    simpa [DAGCircuit.deadVertices] using this
  change n + (sealGates n C.deadVertices (C.gates, C.output)).1.length ≤ 4 * (n + C.gates.length)
  rw [h]
  dsimp only
  simp only [DAGCircuit.size] at hd
  omega

/-- Sealing a circuit whose gates are strict gives a strict circuit: the output is then the
only sink. -/
theorem DAGCircuit.seal_isStrict (hC : ∀ g ∈ C.gates, g.Strict) : C.seal.IsStrict := by
  obtain ⟨ext, hext, hstrict⟩ := (seal_spec C).extends_gates
  refine ⟨fun g hg => ?_, fun v hv hne => ?_⟩
  · change g ∈ (sealGates n C.deadVertices (C.gates, C.output)).1 at hg
    rw [hext, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hC g hg
    · exact hstrict g hg
  · refine sealGates_read C.deadVertices C.gates C.output C.output_lt
      (fun _ hu => (DAGCircuit.mem_deadVertices.mp hu).1) (fun w hw hwo hwL => ?_) v hv hne
    rw [DAGCircuit.mem_deadVertices] at hwL
    have : C.fanout w ≠ 0 := fun h => hwL ⟨hw, hwo, h⟩
    exact Nat.pos_of_ne_zero this

/-- Sealing keeps fan-out at most two when the output is read at most once. -/
theorem DAGCircuit.seal_hasFanoutTwo (hF : C.HasFanoutTwo) (ho : C.fanout C.output ≤ 1) :
    C.seal.HasFanoutTwo :=
  sealGates_fanout C.deadVertices C.gates C.output C.args_lt C.output_lt
    (fun _ hu => (DAGCircuit.mem_deadVertices.mp hu).1)
    (List.Nodup.filter _ List.nodup_range)
    (fun h => (DAGCircuit.mem_deadVertices.mp h).2.1 rfl)
    (fun _ hu => (DAGCircuit.mem_deadVertices.mp hu).2.2) ho hF

end Seal

/-! ## Strictification -/

/-- The strict version of a circuit with at least one input: remove constants and
identity gates (`deconst`), then attach the dead vertices to the output (`seal`). -/
def DAGCircuit.strictify (C : DAGCircuit n) (hn : 0 < n) : DAGCircuit n :=
  (C.deconst hn).seal

section Strictify

variable (C : DAGCircuit n) (hn : 0 < n)

/-- The strict version computes the same function. -/
theorem DAGCircuit.strictify_eval (hC : C.IsFaninTwo) (x : Fin n → Bool) : (C.strictify hn).eval x = C.eval x := by
  rw [DAGCircuit.strictify, DAGCircuit.seal_eval, C.deconst_eval hn hC]

/-- The strict version of a fan-in-two circuit is strict. -/
theorem DAGCircuit.strictify_isStrict (hC : C.IsFaninTwo) : (C.strictify hn).IsStrict :=
  (C.deconst hn).seal_isStrict (C.deconst_strict hn hC)

/-- The strict version has size at most `4S + 12`. -/
theorem DAGCircuit.strictify_size_le : (C.strictify hn).size ≤ 4 * C.size + 12 := by
  have := (C.deconst hn).seal_size_le
  rw [DAGCircuit.deconst_size] at this
  exact this.trans (by omega)

end Strictify

/-- **The relaxed model is the literal model up to a constant factor.**  For `n ≥ 1`, every
fan-in-two circuit of size `S` (constants, identity gates and dead gates allowed) is
equivalent to a circuit of the literal model of [AB09, Def 6.1] — `∧`/`∨` of fan-in exactly
two, `¬` of fan-in one, the inputs as the only sources and the output as the only sink —
of size at most `4S + 12`.  [AB09, Def 6.1]

The hypothesis `n ≥ 1` is necessary: `not_isStrict_zero`.  The book uses its model
directly and has no such statement; it justifies formally that every upper bound proved over
the relaxed model transfers to the literal one.

**Proof sketch.** First (`deconst`) compute `¬x₀`, `1 = x₀ ∨ ¬x₀` and `0 = x₀ ∧ ¬x₀` and
replace each gate by a strict gate reading the renamed vertices: the constant `1` by
`1 ∨ 0`, the constant `0` by `1 ∧ 0`, an identity `∧(a)` by `a ∧ 1`, an identity `∨(a)` by
`a ∨ 0`; this adds three gates.  Then (`seal`) for every vertex `u` other than the output
that no gate reads, append `¬u`, `u ∨ ¬u` and the new output `o ∧ (u ∨ ¬u) = o`; every
formerly unread vertex is now read, every new vertex but the last is read, and the output
value is unchanged.  This adds at most three gates per vertex. -/
theorem DAGCircuit.exists_isStrict (C : DAGCircuit n) (hC : C.IsFaninTwo) (hn : 0 < n) :
    ∃ C' : DAGCircuit n, C'.IsStrict ∧ (∀ x, C'.eval x = C.eval x) ∧
      C'.size ≤ 4 * C.size + 12 :=
  ⟨C.strictify hn, C.strictify_isStrict hn hC, C.strictify_eval hn hC,
    C.strictify_size_le hn⟩

/-- The strict circuits on `n ≥ 1` inputs compute the same functions as the fan-in-two
ones, up to the size bound `4S + 12`; a strict circuit is in particular fan-in two.
[AB09, Def 6.1] -/
theorem DAGCircuit.exists_isStrict_iff (hn : 0 < n) (f : (Fin n → Bool) → Bool) :
    (∃ C : DAGCircuit n, C.IsFaninTwo ∧ ∀ x, C.eval x = f x) ↔
      ∃ C : DAGCircuit n, C.IsStrict ∧ ∀ x, C.eval x = f x := by
  constructor
  · rintro ⟨C, hC, hf⟩
    obtain ⟨C', hC', heq, -⟩ := C.exists_isStrict hC hn
    exact ⟨C', hC', fun x => (heq x).trans (hf x)⟩
  · rintro ⟨C, hC, hf⟩
    exact ⟨C, hC.isFaninTwo, hf⟩

/-! ## Strict circuit families -/

/-- The strict version of a fan-in-two family: the length-`0` circuit is kept (no strict
circuit exists there), every other circuit is strictified. -/
def DAGCircuitFamily.strictify (C : DAGCircuitFamily) : DAGCircuitFamily where
  circuit
    | 0 => C.circuit 0
    | n + 1 => (C.circuit (n + 1)).strictify (Nat.succ_pos n)

/-- The strict version of a fan-in-two family computes the same function at every length. -/
theorem DAGCircuitFamily.strictify_eval (C : DAGCircuitFamily) (hC : C.HasFaninTwo) :
    ∀ n (x : Fin n → Bool), (C.strictify.circuit n).eval x = (C.circuit n).eval x
  | 0, _ => rfl
  | n + 1, x => (C.circuit (n + 1)).strictify_eval _ (hC _) x

end BoolCircuit

/-- `L ∈ SIZE(T)` over the literal model of [AB09, Def 6.1]: some family decides `L`, its
length-`n` circuit of size at most `T n` and strict for every `n ≥ 1`.  At `n = 0` no strict
circuit exists (`BoolCircuit.DAGCircuit.not_isStrict_zero`), so there a fan-in-two circuit
(possibly a constant) is allowed.  [AB09, Def 6.2] -/
def Language.InStrictSIZE (T : ℕ → ℕ) (L : Language Bool) : Prop :=
  ∃ C : BoolCircuit.DAGCircuitFamily, (C.circuit 0).IsFaninTwo ∧
    (∀ n, 0 < n → (C.circuit n).IsStrict) ∧ (∀ n, (C.circuit n).size ≤ T n) ∧ C.language = L

/-- `P/poly` over the literal model of [AB09, Def 6.1] (strict at every `n ≥ 1`).
[AB09, Def 6.5] -/
def Language.InStrictPPoly (L : Language Bool) : Prop :=
  ∃ a k : ℕ, L.InStrictSIZE (fun n => a * (n + 1) ^ k)

/-- A language decided by strict circuits of size `T` is in `SIZE(T)`. -/
theorem Language.InStrictSIZE.inSIZE {T : ℕ → ℕ} {L : Language Bool} (h : L.InStrictSIZE T) :
    L.InSIZE T := by
  obtain ⟨C, h0, hS, hT, hL⟩ := h
  refine ⟨C, fun n => ?_, hT, hL⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact h0
  · exact (hS n hn).isFaninTwo

/-- `strict-SIZE(T) ⊆ strict-SIZE(T')` whenever `T ≤ T'` pointwise. -/
theorem Language.InStrictSIZE.mono {T T' : ℕ → ℕ} {L : Language Bool} (h : L.InStrictSIZE T)
    (hT : ∀ n, T n ≤ T' n) : L.InStrictSIZE T' := by
  obtain ⟨C, h0, hS, hs, hL⟩ := h
  exact ⟨C, h0, hS, fun n => (hs n).trans (hT n), hL⟩

/-- **`SIZE(T) ⊆ strict-SIZE(4T + 12)`**: requiring the literal model of [AB09, Def 6.1] at
every length `n ≥ 1` costs at most a factor `4` and an additive `12` in size.
[AB09, Defs 6.1, 6.2] -/
theorem Language.InSIZE.inStrictSIZE {T : ℕ → ℕ} {L : Language Bool} (h : L.InSIZE T) :
    L.InStrictSIZE fun n => 4 * T n + 12 := by
  obtain ⟨C, hG, hT, hL⟩ := h
  refine ⟨C.strictify, hG 0, fun n hn => ?_, fun n => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
    exact (C.circuit (0 + m + 1)).strictify_isStrict _ (hG _)
  · cases n with
    | zero => exact (hT 0).trans (by dsimp only; omega)
    | succ m =>
      exact ((C.circuit (m + 1)).strictify_size_le _).trans (by have := hT (m + 1); dsimp only; omega)
  · rw [← hL]
    ext w
    simp only [BoolCircuit.DAGCircuitFamily.mem_language_iff,
      BoolCircuit.DAGCircuitFamily.strictify_eval C hG]

/-- **`P/poly` does not depend on the relaxation**: a language is in `P/poly` iff it is
decided by polynomial-size circuits of the literal model of [AB09, Def 6.1] at every length
`n ≥ 1` (with an arbitrary fan-in-two circuit at `n = 0`, where the literal model has
none).  [AB09, Defs 6.1, 6.5] -/
theorem Language.inPPoly_iff_inStrictPPoly (L : Language Bool) :
    L.InPPoly ↔ L.InStrictPPoly := by
  constructor
  · rintro ⟨a, k, h⟩
    refine ⟨4 * a + 12, k, h.inStrictSIZE.mono fun n => ?_⟩
    have : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (Nat.succ_pos n)
    nlinarith
  · rintro ⟨a, k, h⟩
    exact ⟨a, k, h.inSIZE⟩
