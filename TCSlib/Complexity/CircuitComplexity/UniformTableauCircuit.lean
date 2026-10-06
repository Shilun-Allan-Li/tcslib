/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.List.Dedup
import TCSlib.Complexity.CircuitComplexity.PSubsetPPolyProgram

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A regular compilation of gadget programs

`BoolCircuit.progCircuit` (`PSubsetPPolyProgram.lean`) compiles a gadget program into a
circuit whose vertex numbering depends on the kinds of all earlier instructions and whose
gates merge coinciding sources; that is the right object for [AB09, Thm 6.6] but hard to
*print* by a machine.  This file gives a second compilation, `BoolCircuit.tabCircuit`,
designed to be emitted by a polynomial-time machine ([AB09, Remark 6.7]; the regular
layout is also intended to make a logarithmic-space emitter natural): every instruction
occupies exactly `W` consecutive vertices,
instruction `i` starting at `tabBase i = n + 2 + |z| + W (i + 1)`, laid out as

* `m` *copy gates*, the `s`-th reading the vertex of the instruction's `s`-th source;
* the gadgets of its kind (`BoolCircuit.embedAll`), reading the copy gates — the same gate
  list for every instruction of that kind, shifted by the base;
* constant padding up to `G` gadget gates (`G` the largest gadget width of a kind);
* `w` *output copies*, the `j`-th holding bit `j` of the instruction's block, at the fixed
  offset `m + G + j`.

The program's input is a *virtual input* `z ++ x`: its first `|z|` bits are constants (gates
of the circuit, "hard-wired" [AB09, p. 113]) and the rest are the circuit's `n` inputs.
This is how the Cook–Levin circuit of [AB09, Lem 6.10] fixes the input `x` and leaves the
certificate free.

## Main definitions

* `BoolCircuit.tabCircuit m w F n z prog o j` — the circuit, with output bit `j` of block `o`.
* `BoolCircuit.tabBase`, `BoolCircuit.tabSrc`, `BoolCircuit.tabFixed` — the layout.

## Main results

* `BoolCircuit.tabCircuit_eval` — the circuit computes the program's blocks on the virtual
  input `z ++ x`.
* `BoolCircuit.tabCircuit_isFaninTwo`, `BoolCircuit.tabCircuit_size` — fan-in two, and
  size `n + 2 + |z| + W (|prog| + 1)`.

## Divergences from [AB09]

* Applied to the configuration-tableau program (`UniformTableauSpec.lean`) this is the
  non-oblivious tableau, of size `O(T (T + n))` for `T` steps — not the book's `O(T)`-size
  circuit for an oblivious machine (Thm 6.6); for P-uniformity only polynomiality matters.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, proof of Theorem 6.6; §6.2, Remark 6.7.)
-/

namespace BoolCircuit

/-! ## Gate shapes -/

/-- The gate copying vertex `v` (an `∧` of fan-in one). -/
def copyGate (v : ℕ) : DAGGate := ⟨.and, [v]⟩

/-- The gate `g` with every argument shifted by `B`. -/
def shiftGate (B : ℕ) (g : DAGGate) : DAGGate := ⟨g.kind, g.args.map (B + ·)⟩

/-- A copy gate evaluates to the copied vertex. -/
@[simp] theorem copyGate_eval (v : ℕ) (vals : List Bool) :
    (copyGate v).eval vals = vals.getD v false := by
  simp [copyGate, DAGGate.eval]

/-- **Embedding gadgets on consecutive sources is a shift**: wiring the gadgets `Ds` to the
sources `B, …, B + m − 1` after `B + L` vertices is the gate list for sources `0, …, m − 1`
after `L` vertices, with every argument shifted by `B`.

**Proof sketch.** On consecutive sources the renaming `embedMap` is `v ↦ B + v'` where `v'`
is the renaming for sources `0, …, m − 1`; merging repeated arguments commutes with the
injective shift (`List.dedup_map_of_injective`); induction over the gadget list. -/
theorem embedAll_range'_eq {m : ℕ} (Ds : List (DAGCircuit m)) (B L : ℕ) :
    embedAll Ds (List.range' B m) (B + L) = (embedAll Ds (List.range m) L).map (shiftGate B) := by
  have hmap : ∀ L v, embedMap m (B + L) (List.range' B m) v = B + embedMap m L (List.range
      m) v := by
    intro L v
    unfold embedMap
    split_ifs with hv
    · rw [List.getD_eq_getElem _ _ (by simpa using hv), List.getD_eq_getElem _ _ (by simpa using
        hv)]
      simp
    · omega
  induction Ds generalizing L with
  | nil => rfl
  | cons D Ds ih =>
    simp only [embedAll, List.map_append]
    rw [show B + L + (D.gates.length + 1) = B + (L + (D.gates.length + 1)) by omega, ih]
    congr 1
    simp only [embedGates, List.map_append, List.map_map, List.map_cons, List.map_nil]
    congr 1
    · apply List.map_congr_left
      intro g _
      simp only [DAGGate.remap, DAGGate.dedupArgs]
      congr 1
      rw [← List.dedup_map_of_injective (f := (B + ·)) (fun a b h => by simpa using h)]
      congr 1
      simp only [List.map_map]
      apply List.map_congr_left
      intro v _
      simp [hmap]
    · simp [shiftGate, hmap]

/-! ## The layout -/

variable {κ : Type} [Fintype κ] (m w : ℕ) (F : κ → List Bool → List Bool)

/-- The gadget-gate budget of an instruction: the largest gate count of a kind. -/
noncomputable def tabG : ℕ := Finset.univ.sup (kindWidth m w F)

/-- The number of vertices of an instruction: `m` copies, `G` gadget gates, `w` outputs. -/
noncomputable def tabW : ℕ := m + tabG m w F + w

/-- Every kind's gadgets fit the budget. -/
theorem kindWidth_le_tabG (κ₀ : κ) : kindWidth m w F κ₀ ≤ tabG m w F :=
  Finset.le_sup (f := kindWidth m w F) (Finset.mem_univ κ₀)

variable (n : ℕ) (z : List Bool)

/-- The first vertex of instruction `i`: after the `n` inputs, the two constants, the `|z|`
hard-wired bits and `W` padding vertices. -/
noncomputable def tabBase (i : ℕ) : ℕ := n + 2 + z.length + tabW m w F * (i + 1)

/-- The vertex read for a source of instruction `i`: input `k` of the virtual input is the
hard-wired gate `n + 2 + k` if `k < |z|` and circuit input `k − |z|` otherwise; constants are
the vertices `n` (`0`) and `n + 1` (`1`); bit `j` of block `i'` is output copy `j` of
instruction `i'`.  Invalid sources read the constant `0`. -/
noncomputable def tabSrc (i : ℕ) (s : BitSrc) : ℕ :=
  if s.Valid (z.length + n) w i then
    match s with
    | .input k => if k < z.length then n + 2 + k else k - z.length
    | .const b => if b then n + 1 else n
    | .block i' j => tabBase m w F n z i' + m + tabG m w F + j
  else n

/-- The fixed part of an instruction of kind `κ₀`, relative to its base: the gadgets reading
the copy gates `0, …, m − 1`, padding, and the output copies. -/
noncomputable def tabFixed (κ₀ : κ) : List DAGGate :=
  embedAll (kindGadgets m w F κ₀) (List.range m) m ++
    List.replicate (tabG m w F - kindWidth m w F κ₀) (constGate true) ++
    (List.range w).map (fun j => copyGate (m + embedOffset (kindGadgets m w F κ₀) j))

/-- The sources of an instruction, padded or truncated to exactly `m`. -/
def padSrc (srcs : List BitSrc) : List BitSrc :=
  (srcs ++ List.replicate m (BitSrc.const false)).take m

/-- The gates of instruction `i`: copies of its sources, then its fixed part shifted to its
base. -/
noncomputable def tabInstrGates (i : ℕ) (ins : GInstr κ) : List DAGGate :=
  (padSrc m ins.srcs).map (fun s => copyGate (tabSrc m w F n z i s)) ++
    (tabFixed m w F ins.kind).map (shiftGate (tabBase m w F n z i))

/-- The gates before the instructions: the constants `0` and `1`, the hard-wired bits, and
`W` padding vertices. -/
def tabPre (W : ℕ) : List DAGGate :=
  [constGate false, constGate true] ++ z.map constGate ++ List.replicate W (constGate false)

/-- The gates of the instructions `prog`, the first being instruction `i`. -/
noncomputable def tabProgGates : ℕ → List (GInstr κ) → List DAGGate
  | _, [] => []
  | i, ins :: prog => tabInstrGates m w F n z i ins ++ tabProgGates (i + 1) prog

/-! ## Lengths and acyclicity -/

/-- The fixed part has `G + w` gates. -/
theorem length_tabFixed (κ₀ : κ) : (tabFixed m w F κ₀).length = tabG m w F + w := by
  have := kindWidth_le_tabG m w F κ₀
  simp only [tabFixed, List.length_append, length_embedAll, List.length_replicate,
    List.length_map, List.length_range, kindWidth] at this ⊢
  omega

/-- The padded source list has `m` entries. -/
@[simp] theorem length_padSrc (srcs : List BitSrc) : (padSrc m srcs).length = m := by
  simp [padSrc]

/-- Every instruction has `W` gates. -/
theorem length_tabInstrGates (i : ℕ) (ins : GInstr κ) :
    (tabInstrGates m w F n z i ins).length = tabW m w F := by
  simp [tabInstrGates, length_tabFixed, tabW]; omega

/-- The instruction gates of `prog` number `W · |prog|`. -/
theorem length_tabProgGates (i : ℕ) (prog : List (GInstr κ)) :
    (tabProgGates m w F n z i prog).length = tabW m w F * prog.length := by
  induction prog generalizing i with
  | nil => simp [tabProgGates]
  | cons ins prog ih =>
    simp [tabProgGates, length_tabInstrGates, ih, Nat.mul_succ]; omega

/-- The prefix has `2 + |z| + W` gates. -/
@[simp] theorem length_tabPre (W : ℕ) : (tabPre z W).length = 2 + z.length + W := by
  simp [tabPre]; omega

/-- A source vertex of instruction `i` precedes the instruction. -/
theorem tabSrc_lt (i : ℕ) (s : BitSrc) : tabSrc m w F n z i s < tabBase m w F n z i := by
  have hW : tabW m w F * 1 ≤ tabW m w F * (i + 1) := Nat.mul_le_mul_left _ (by omega)
  unfold tabSrc tabBase
  split_ifs with hv
  · cases s with
    | input k =>
      simp only [BitSrc.Valid] at hv
      dsimp only; split_ifs <;> omega
    | const b => cases b <;> simp <;> omega
    | block i' j =>
      obtain ⟨hi, hj⟩ := hv
      dsimp only
      have : tabW m w F * (i' + 1) + tabW m w F ≤ tabW m w F * (i + 1) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
      unfold tabBase tabW at *
      omega
  · omega

/-- The gates of instruction `i` read only earlier vertices.

**Proof sketch.** Copy gates read source vertices, all below the base (`tabSrc_lt`); the
fixed part is acyclic relative to `m` (`gatesAcyclic_embedAll`, constants, output copies
reading gadget outputs) and the shift by the base preserves this. -/
theorem gatesAcyclic_tabInstrGates (i : ℕ) (ins : GInstr κ) :
    GatesAcyclic (tabBase m w F n z i) (tabInstrGates m w F n z i ins) := by
  set B := tabBase m w F n z i
  have hcopies : GatesAcyclic B ((padSrc m ins.srcs).map
      (fun s => copyGate (tabSrc m w F n z i s))) := by
    intro q hq a ha
    simp only [List.getElem_map, copyGate, List.mem_singleton] at ha
    subst ha
    have := tabSrc_lt m w F n z i ((padSrc m ins.srcs)[q]'(by simpa using hq))
    omega
  have hfix : GatesAcyclic m (tabFixed m w F ins.kind) := by
    have h1 := gatesAcyclic_embedAll (kindGadgets m w F ins.kind) (List.range m) m
      (by simp) (fun a ha => by simpa using ha)
    refine (h1.append ?_).append ?_
    · intro q hq a ha; simp at ha
    · intro q hq a ha
      simp only [List.getElem_map, List.getElem_range, copyGate, List.mem_singleton] at ha
      subst ha
      have hlt := embedOffset_lt (kindGadgets m w F ins.kind) (j := q) (by simpa using hq)
      have hk := kindWidth_le_tabG m w F ins.kind
      simp only [kindWidth, List.length_append, length_embedAll, List.length_replicate] at hk ⊢
      omega
  refine hcopies.append ?_
  simp only [List.length_map, length_padSrc]
  intro q hq a ha
  simp only [List.length_map] at hq
  simp only [List.getElem_map, shiftGate, List.mem_map] at ha
  obtain ⟨a', ha', rfl⟩ := ha
  have := hfix q hq a' ha'
  omega

/-- The instruction gates read only earlier vertices. -/
theorem gatesAcyclic_tabProgGates (i : ℕ) (prog : List (GInstr κ)) :
    GatesAcyclic (tabBase m w F n z i) (tabProgGates m w F n z i prog) := by
  induction prog generalizing i with
  | nil => exact GatesAcyclic.nil
  | cons ins prog ih =>
    refine (gatesAcyclic_tabInstrGates m w F n z i ins).append ?_
    rw [length_tabInstrGates, show tabBase m w F n z i + tabW m w F = tabBase m w F n z (i + 1) by
      simp only [tabBase, Nat.mul_succ]; omega]
    exact ih (i + 1)

/-- The prefix gates are constants. -/
theorem mem_tabPre {W : ℕ} {g : DAGGate} (hg : g ∈ tabPre z W) : ∃ b, g = constGate b := by
  simp only [tabPre, List.mem_append, List.mem_cons, List.mem_map, List.mem_replicate,
    List.not_mem_nil, or_false] at hg
  rcases hg with (h | h) | h
  · rcases h with rfl | rfl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  · obtain ⟨b, -, rfl⟩ := h; exact ⟨b, rfl⟩
  · exact ⟨false, h.2⟩

/-- The prefix gates read nothing. -/
theorem gatesAcyclic_tabPre (W : ℕ) : GatesAcyclic n (tabPre z W) := by
  intro q hq a ha
  obtain ⟨b, hb⟩ := mem_tabPre z (List.getElem_mem hq)
  rw [hb] at ha
  cases b <;> simp [constGate] at ha

/-! ## The circuit -/

/-- **The regular tableau circuit** of a gadget program on `n` inputs with hard-wired prefix
`z`: the prefix gates, then `W` vertices per instruction; the output is bit `j` of block `o`
(the constant `0` if out of range). -/
noncomputable def tabCircuit (prog : List (GInstr κ)) (o j : ℕ) : DAGCircuit n where
  gates := tabPre z (tabW m w F) ++ tabProgGates m w F n z 0 prog
  output := if o < prog.length ∧ j < w then tabBase m w F n z o + m + tabG m w F + j else n
  args_lt := by
    refine (gatesAcyclic_tabPre n z _).append ?_
    rw [length_tabPre, show n + (2 + z.length + tabW m w F) = tabBase m w F n z 0 by
      simp [tabBase]; omega]
    exact gatesAcyclic_tabProgGates m w F n z 0 prog
  output_lt := by
    simp only [List.length_append, length_tabPre, length_tabProgGates]
    split_ifs with h
    · have : tabW m w F * (o + 1) + tabW m w F ≤ tabW m w F * (prog.length + 1) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
      simp only [tabBase, tabW] at this ⊢
      nlinarith
    · omega

/-- The size of the tableau circuit: `n + 2 + |z| + W (|prog| + 1)`. -/
theorem tabCircuit_size (prog : List (GInstr κ)) (o j : ℕ) :
    (tabCircuit m w F n z prog o j).size = n + 2 + z.length + tabW m w F * (prog.length + 1) := by
  simp only [DAGCircuit.size, tabCircuit, List.length_append, length_tabPre, length_tabProgGates]
  ring

/-- The tableau circuit has fan-in at most two.

**Proof sketch.** Constant gates read nothing, copy gates read one vertex, and the gadget
gates are fan-in two (`faninTwo_embedAll`, `gadget_isFaninTwo`); shifting by the base is
injective, so duplicate-freeness and arities are kept. -/
theorem tabCircuit_isFaninTwo (prog : List (GInstr κ)) (o j : ℕ) :
    (tabCircuit m w F n z prog o j).IsFaninTwo := by
  have key : ∀ g ∈ (tabCircuit m w F n z prog o j).gates,
      g.args.Nodup ∧ (g.kind = .not → g.args.length = 1) ∧ g.args.length ≤ 2 := by
    have hconst : ∀ b, (constGate b).args.Nodup ∧ ((constGate b).kind = .not →
        (constGate b).args.length = 1) ∧ (constGate b).args.length ≤ 2 := by
      intro b; cases b <;> simp [constGate]
    have hcopy : ∀ v, (copyGate v).args.Nodup ∧ ((copyGate v).kind = .not →
        (copyGate v).args.length = 1) ∧ (copyGate v).args.length ≤ 2 := by
      intro v; simp [copyGate]
    have hshift : ∀ B (g : DAGGate), (g.args.Nodup ∧ (g.kind = .not → g.args.length = 1) ∧
        g.args.length ≤ 2) → ((shiftGate B g).args.Nodup ∧ ((shiftGate B g).kind = .not →
          (shiftGate B g).args.length = 1) ∧ (shiftGate B g).args.length ≤ 2) := by
      intro B g ⟨h1, h2, h3⟩
      refine ⟨h1.map (fun a b h => by simpa using h), by simpa [shiftGate] using h2,
        by simpa [shiftGate] using h3⟩
    have hfix : ∀ κ₀ g, g ∈ tabFixed m w F κ₀ →
        g.args.Nodup ∧ (g.kind = .not → g.args.length = 1) ∧ g.args.length ≤ 2 := by
      intro κ₀ g hg
      simp only [tabFixed, List.mem_append, List.mem_replicate, List.mem_map,
        List.mem_range] at hg
      rcases hg with (hg | ⟨-, rfl⟩) | ⟨j, -, rfl⟩
      · refine faninTwo_embedAll _ (fun D hD => ?_) _ _ g hg
        simp only [kindGadgets, List.mem_map, List.mem_range] at hD
        obtain ⟨j, -, rfl⟩ := hD
        exact gadget_isFaninTwo _
      · exact hconst true
      · exact hcopy _
    have hprog : ∀ i (prog : List (GInstr κ)), ∀ g ∈ tabProgGates m w F n z i prog,
        g.args.Nodup ∧ (g.kind = .not → g.args.length = 1) ∧ g.args.length ≤ 2 := by
      intro i prog
      induction prog generalizing i with
      | nil => simp [tabProgGates]
      | cons ins prog ih =>
        intro g hg
        simp only [tabProgGates, tabInstrGates, List.mem_append, List.mem_map] at hg
        rcases hg with (⟨s, -, rfl⟩ | ⟨g', hg', rfl⟩) | hg
        · exact hcopy _
        · exact hshift _ _ (hfix _ g' hg')
        · exact ih _ g hg
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨b, rfl⟩ := mem_tabPre z hg
      exact hconst b
    · exact hprog 0 prog g hg
  exact ⟨fun g hg => ⟨(key g hg).1, (key g hg).2.1⟩, fun g hg => (key g hg).2.2⟩

/-! ## Correctness -/

/-- Running copy gates of earlier vertices appends the copied values. -/
theorem runWith_copies (V : List Bool) (vs : List ℕ) (h : ∀ v ∈ vs, v < V.length) :
    runWith DAGGate.eval (vs.map copyGate) V = V ++ vs.map (fun v => V.getD v false) := by
  induction vs generalizing V with
  | nil => simp
  | cons v vs ih =>
    rw [List.map_cons, runWith_cons, copyGate_eval, ih _ (fun u hu => by
      have := h u (by simp [hu]); simp; omega)]
    simp only [List.map_cons, List.append_assoc, List.singleton_append]
    congr 2
    apply List.map_congr_left
    intro u hu
    rw [List.getD_append _ _ _ _ (h u (by simp [hu]))]

/-- The instruction gates of a concatenation. -/
theorem tabProgGates_append (i : ℕ) (p q : List (GInstr κ)) :
    tabProgGates m w F n z i (p ++ q) =
      tabProgGates m w F n z i p ++ tabProgGates m w F n z (i + p.length) q := by
  induction p generalizing i with
  | nil => simp [tabProgGates]
  | cons ins p ih =>
    simp only [List.cons_append, tabProgGates, ih, List.append_assoc, List.length_cons]
    congr 3; omega

/-- The prefix values: the inputs, the two constants, the hard-wired bits, padding. -/
theorem runWith_tabPre (x : List Bool) (W : ℕ) :
    runWith DAGGate.eval (tabPre z W) x = x ++ ([false, true] ++ z ++ List.replicate W false) := by
  have : tabPre z W = ([false, true] ++ z ++ List.replicate W false).map constGate := by
    simp [tabPre, List.map_replicate]
  rw [this, runWith_eval_constGates]

/-- The instruction-region invariant: the values of the vertices of instruction `i' < i`'s
output copies are the program's blocks, on top of the prefix values. -/
private def TabInv (x : Fin n → Bool) (prog : List (GInstr κ)) (i : ℕ) (V : List Bool) : Prop :=
  V.length = tabBase m w F n z i ∧
  (∀ k : Fin n, V.getD k false = x k) ∧ V.getD n false = false ∧ V.getD (n + 1) false = true ∧
  (∀ k < z.length, V.getD (n + 2 + k) false = z.getD k false) ∧
  ∀ i' < i, ∀ j < w, V.getD (tabBase m w F n z i' + m + tabG m w F + j) false =
    ((progBlocks F (z ++ List.ofFn x) prog).getD i' []).getD j false

/-- A valid source reads, at its vertex, its value on the virtual input.

**Proof sketch.** Case on the source. An input bit `k` is read either from the hard-wired
prefix `z` (if `k < |z|`) or from the circuit input `x` at position `k - |z|`; the
constants `0`/`1` are read from the two constant vertices; a block bit is read from the
output copy of an earlier instruction, which holds that block by the invariant. -/
private theorem tabSrc_eval {x : Fin n → Bool} {prog : List (GInstr κ)} {i : ℕ} {V : List Bool}
    (hV : TabInv m w F n z x prog i V) {s : BitSrc} (hs : s.Valid (z.length + n) w i) :
    V.getD (tabSrc m w F n z i s) false =
      BitSrc.eval (z ++ List.ofFn x) (progBlocks F (z ++ List.ofFn x) prog) s := by
  obtain ⟨-, hin, h0, h1, hz, hb⟩ := hV
  unfold tabSrc
  rw [if_pos hs]
  cases s with
  | input k =>
    simp only [BitSrc.Valid] at hs
    simp only [BitSrc.eval]
    split_ifs with hk
    · rw [hz k hk, List.getD_append _ _ _ _ hk]
    · rw [List.getD_append_right _ _ _ _ (by omega)]
      have := hin ⟨k - z.length, by omega⟩
      simp only at this
      rw [this, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  | const b =>
    cases b
    · simp only [BitSrc.eval, Bool.false_eq_true, if_false]; exact h0
    · simp only [BitSrc.eval, if_true]; exact h1
  | block i' j => exact hb i' hs.1 j hs.2

/-- **One instruction preserves the invariant**: after the gates of instruction `i` the
output copies of instruction `i` hold its block.

**Proof sketch.** The copy gates put the source values (`tabSrc_eval`) at the base; the
gadgets of the kind, a shift of `embedAll` on these consecutive vertices
(`embedAll_range'_eq`), compute the bits of the kind's function on them
(`runWith_embedAll_getD`, `gadget_eval`), which is the block (`progBlocks_getD`); the output
copies copy them. -/
private theorem tabInv_succ {x : Fin n → Bool} {prog : List (GInstr κ)}
    (hwf : ProgWF (z.length + n) w prog) (hm : ∀ ins ∈ prog, ins.srcs.length = m) {i : ℕ}
    (hi : i < prog.length) {V : List Bool} (hV : TabInv m w F n z x prog i V) :
    TabInv m w F n z x prog (i + 1)
      (runWith DAGGate.eval (tabInstrGates m w F n z i prog[i]) V) := by
  have hlen : V.length = tabBase m w F n z i := hV.1
  have hmi : prog[i].srcs.length = m := hm _ (List.getElem_mem hi)
  have hsrcs : padSrc m prog[i].srcs = prog[i].srcs := by
    rw [padSrc, List.take_left' hmi]
  generalize hB : tabBase m w F n z i = B at hlen
  generalize hins : prog[i] = ins at hmi hsrcs
  generalize hDs : kindGadgets m w F ins.kind = Ds
  have hDsl : Ds.length = w := by simp [← hDs]
  have hk : embedWidth Ds ≤ tabG m w F := by
    have := kindWidth_le_tabG m w F ins.kind; rwa [kindWidth, hDs] at this
  -- the copies
  have hcopy : runWith DAGGate.eval ((padSrc m ins.srcs).map
      (fun s => copyGate (tabSrc m w F n z i s))) V =
      V ++ ins.srcs.map (fun s => V.getD (tabSrc m w F n z i s) false) := by
    rw [hsrcs, show ins.srcs.map (fun s => copyGate (tabSrc m w F n z i s)) =
      (ins.srcs.map (tabSrc m w F n z i)).map copyGate by simp, runWith_copies V _ (fun v hv => by
      obtain ⟨s, -, rfl⟩ := List.mem_map.mp hv; rw [hlen, ← hB]; exact tabSrc_lt m w F n z i s)]
    simp [List.map_map, Function.comp_def]
  generalize hVc : V ++ ins.srcs.map (fun s => V.getD (tabSrc m w F n z i s) false) = Vc at hcopy
  have hVcl : Vc.length = B + m := by rw [← hVc]; simp [hlen, hmi]
  have hVc_src : ∀ s (hs : s < m), Vc.getD (B + s) false =
      BitSrc.eval (z ++ List.ofFn x) (progBlocks F (z ++ List.ofFn x) prog)
        (ins.srcs[s]'(by omega)) := by
    intro s hs
    rw [← hVc, List.getD_append_right _ _ _ _ (by omega), hlen, Nat.add_sub_cancel_left,
      List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map]
    have hmem : ins.srcs[s]'(by omega) ∈ prog[i].srcs := by
      rw [hins]; exact List.getElem_mem _
    exact tabSrc_eval m w F n z hV (hwf i hi _ hmem)
  -- the fixed part
  have hfix : (tabFixed m w F ins.kind).map (shiftGate B) =
      embedAll Ds (List.range' B m) (B + m) ++
        (List.replicate (tabG m w F - embedWidth Ds) (constGate true) ++
        (List.range w).map (fun j => copyGate (B + m + embedOffset Ds j))) := by
    rw [tabFixed, List.map_append, List.map_append, ← embedAll_range'_eq, kindWidth, hDs,
      List.append_assoc]
    congr 2
    · simp [List.map_replicate, shiftGate, constGate]
    · simp only [List.map_map]
      apply List.map_congr_left
      intro j _
      simp [shiftGate, copyGate, Nat.add_assoc]
  generalize hVe : runWith DAGGate.eval (embedAll Ds (List.range' B m) (B + m)) Vc = Ve
  have hVel : Ve.length = B + m + embedWidth Ds := by rw [← hVe]; simp [hVcl]
  have hgad : ∀ j < w, Ve.getD (B + m + embedOffset Ds j) false =
      ((progBlocks F (z ++ List.ofFn x) prog).getD i []).getD j false := by
    intro j hj
    have key := runWith_embedAll_getD Ds (List.range' B m) (by simp) Vc
      (fun a ha => by rw [hVcl]; simp at ha; omega) (j := j) (by omega)
    rw [hVcl] at key
    rw [← hVe, key, progBlocks_getD F _ prog hwf hi, hins]
    simp only [← hDs, kindGadgets, List.getElem_map, List.getElem_range, gadget_eval]
    congr 2
    apply List.ext_getElem (by simp [hmi])
    intro s h1 h2
    simp only [List.getElem_ofFn, List.length_ofFn] at h1 ⊢
    have hr : (List.range' B m).getD s 0 = B + s := by
      rw [List.getD_eq_getElem _ _ (by simpa using h1)]; simp
    rw [hr, hVc_src s h1, List.getElem_map]
  have hVd : runWith DAGGate.eval (List.replicate (tabG m w F - embedWidth Ds) (constGate true)) Ve
      = Ve ++ List.replicate (tabG m w F - embedWidth Ds) true := by
    have := runWith_eval_constGates (List.replicate (tabG m w F - embedWidth Ds) true) Ve
    simpa [List.map_replicate] using this
  generalize hVd' : Ve ++ List.replicate (tabG m w F - embedWidth Ds) true = Vd at hVd
  have hVdl : Vd.length = B + m + tabG m w F := by rw [← hVd']; simp [hVel]; omega
  have hout : runWith DAGGate.eval ((List.range w).map
      (fun j => copyGate (B + m + embedOffset Ds j))) Vd =
      Vd ++ (List.range w).map (fun j => Vd.getD (B + m + embedOffset Ds j) false) := by
    rw [show (List.range w).map (fun j => copyGate (B + m + embedOffset Ds j)) =
      ((List.range w).map (fun j => B + m + embedOffset Ds j)).map copyGate by simp,
      runWith_copies]
    · simp [List.map_map, Function.comp_def]
    · intro v hv
      simp only [List.mem_map, List.mem_range] at hv
      obtain ⟨j, hj, rfl⟩ := hv
      have := embedOffset_lt Ds (j := j) (by omega)
      omega
  have hall : runWith DAGGate.eval (tabInstrGates m w F n z i ins) V =
      Vd ++ (List.range w).map (fun j => Vd.getD (B + m + embedOffset Ds j) false) := by
    rw [tabInstrGates, runWith_append, hcopy, hB, hfix, runWith_append, runWith_append, hVe, hVd,
      hout]
  have hprefix : ∀ v < B, (runWith DAGGate.eval (tabInstrGates m w F n z i ins) V).getD v false =
      V.getD v false := fun v hv => runWith_getD_of_lt _ _ _ (by omega) _
  obtain ⟨-, hin, h0, h1, hz, hb⟩ := hV
  have hBn : n + 2 + z.length ≤ B := by rw [← hB, tabBase]; omega
  refine ⟨?_, fun k => ?_, ?_, ?_, fun k hk' => ?_, fun i' hi' j hj => ?_⟩
  · rw [hall]; simp only [List.length_append, List.length_map, List.length_range, hVdl, ← hB,
      tabBase, tabW]; ring
  · rw [hprefix k (by omega)]; exact hin k
  · rw [hprefix n (by omega)]; exact h0
  · rw [hprefix (n + 1) (by omega)]; exact h1
  · rw [hprefix _ (by omega)]; exact hz k hk'
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi' | rfl
    · have hlt : tabBase m w F n z i' + m + tabG m w F + j < B := by
        have : tabW m w F * (i' + 1) + tabW m w F ≤ tabW m w F * (i + 1) := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
        rw [← hB]; simp only [tabBase, tabW] at this ⊢; omega
      rw [hprefix _ hlt]; exact hb i' hi' j hj
    · rw [hall, hB, List.getD_append_right _ _ _ _ (by omega), hVdl,
        show B + m + tabG m w F + j - (B + m + tabG m w F) = j by omega,
        List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range,
        ← hVd', List.getD_append _ _ _ _ (by
          have := embedOffset_lt Ds (j := j) (by omega)
          rw [hVel]; omega)]
      exact hgad j hj

/-- **The tableau circuit computes the program's blocks**: for a well-formed program with
`m` sources per instruction, on input `x` the circuit outputs bit `j` of block `o` of the
program run on the virtual input `z ++ x`.

**Proof sketch.** The prefix gates hold the inputs, the constants and the hard-wired bits
(`runWith_tabPre`); by induction over the instructions, after instruction `i` the output
copies of every instruction `i' ≤ i` hold its block (`tabInv_succ`); the output vertex is the
output copy `j` of instruction `o`. -/
theorem tabCircuit_eval (prog : List (GInstr κ)) (hwf : ProgWF (z.length + n) w prog)
    (hm : ∀ ins ∈ prog, ins.srcs.length = m) {o j : ℕ} (ho : o < prog.length) (hj : j < w)
    (x : Fin n → Bool) :
    (tabCircuit m w F n z prog o j).eval x =
      ((progBlocks F (z ++ List.ofFn x) prog).getD o []).getD j false := by
  set P0 := runWith DAGGate.eval (tabPre z (tabW m w F)) (List.ofFn x) with hP0
  have hP0v : P0 = List.ofFn x ++ ([false, true] ++ z ++ List.replicate (tabW m w F) false) :=
    runWith_tabPre z _ _
  have h0 : TabInv m w F n z x prog 0 P0 := by
    refine ⟨?_, fun k => ?_, ?_, ?_, fun k hk => ?_, fun i' hi' => absurd hi' (Nat.not_lt_zero _)⟩
    · rw [hP0v]; simp [tabBase]; omega
    · rw [hP0v, List.getD_append _ _ _ _ (by simp)]; simp
    · rw [hP0v, List.getD_append_right _ _ _ _ (by simp)]; simp
    · rw [hP0v, List.getD_append_right _ _ _ _ (by simp)]; simp
    · rw [hP0v, List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_ofFn, show n + 2 + k - n = 2 + k by omega]
      rw [List.append_assoc, List.getD_append_right _ _ _ _ (by simp),
        List.getD_append _ _ _ _ (by simp; omega)]
      simp
  have key : ∀ i ≤ prog.length, TabInv m w F n z x prog i
      (runWith DAGGate.eval (tabProgGates m w F n z 0 (prog.take i)) P0) := by
    intro i
    induction i with
    | zero => simpa [tabProgGates] using h0
    | succ i ih =>
      intro hi
      rw [List.take_succ_eq_append_getElem (by omega), tabProgGates_append, runWith_append,
        List.length_take_of_le (by omega), Nat.zero_add]
      have := tabInv_succ m w F n z hwf hm (i := i) (by omega) (ih (by omega))
      simpa [tabProgGates] using this
  have hfin := (key prog.length le_rfl).2.2.2.2.2 o ho j hj
  rw [List.take_length] at hfin
  simp only [DAGCircuit.eval, DAGCircuit.values, tabCircuit, if_pos (And.intro ho hj),
    runWith_append]
  rw [← hP0, hfin]

end BoolCircuit
