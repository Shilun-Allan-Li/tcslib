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
# Gadget programs

A **gadget program** is a list of instructions, each computing a block of `w` bits by a
fixed finite function `F κ` (its *kind* `κ`) of `m` source bits; a source bit is an input
bit, a constant, or a bit of an earlier block.  This is the shape of every
"constant-size circuit per step" simulation in [AB09, §6.1] (the proof of Thm 6.6 and its
variants): this file compiles such a program into one fan-in-two `BoolCircuit.DAGCircuit`
whose size is `n + 2 + Σᵢ W(κᵢ)`, with `W(κ)` the size of the gadgets of kind `κ`
(`BoolCircuit.gadget`), and proves that the compiled circuit computes the program's
blocks.  The reasoning about a simulation is thus done on the program's blocks
(`BoolCircuit.progBlocks`), where every block satisfies its defining equation
(`BoolCircuit.progBlocks_getD`), and never on gates.

## Main definitions

* `BoolCircuit.BitSrc`, `BoolCircuit.GInstr` — sources and instructions.
* `BoolCircuit.progBlocks F x prog` — the blocks a program computes on the input `x`.
* `BoolCircuit.ProgWF` — every source of instruction `i` is an input below `n`, a constant,
  or a bit `< w` of a block `< i`.
* `BoolCircuit.progCircuit` — the compiled circuit, with output bit `j` of block `i`.

## Main results

* `BoolCircuit.progBlocks_getD` — the defining equation of each block.
* `BoolCircuit.progCircuit_eval` — the compiled circuit outputs the designated bit.
* `BoolCircuit.progCircuit_isFaninTwo`, `BoolCircuit.progCircuit_size_le` — fan-in two and
  size at most `n + 2 + |prog| · W` for finitely many kinds.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, proof of Theorem 6.6, pp. 109–110.)
-/

namespace BoolCircuit

/-! ## Programs and their semantics -/

/-- A source bit of an instruction: input bit `k`, a constant, or bit `j` of block `i`. -/
inductive BitSrc where
  /-- Input bit `k`. -/
  | input (k : ℕ)
  /-- The constant `b`. -/
  | const (b : Bool)
  /-- Bit `j` of the block computed by instruction `i`. -/
  | block (i j : ℕ)
  deriving DecidableEq, Repr

/-- An instruction of a gadget program: its kind and its source bits. -/
structure GInstr (κ : Type) where
  /-- The kind, selecting the finite function computed. -/
  kind : κ
  /-- The source bits, in order. -/
  srcs : List BitSrc

/-- The value of a source bit on input `x`, given the blocks computed so far. -/
def BitSrc.eval (x : List Bool) (bs : List (List Bool)) : BitSrc → Bool
  | .input k => x.getD k false
  | .const b => b
  | .block i j => (bs.getD i []).getD j false

/-- A source is valid for instruction `i` of a program on `n` inputs with block width `w`:
an input below `n`, a constant, or a bit below `w` of an earlier block. -/
def BitSrc.Valid (n w i : ℕ) : BitSrc → Prop
  | .input k => k < n
  | .const _ => True
  | .block i' j => i' < i ∧ j < w

instance (n w i : ℕ) (s : BitSrc) : Decidable (s.Valid n w i) := by
  cases s <;> unfold BitSrc.Valid <;> infer_instance

section Semantics

variable {κ : Type} (F : κ → List Bool → List Bool)

/-- Run the instructions after the blocks `init`: each appends `F κ` of its sources. -/
def progRun (x : List Bool) (prog : List (GInstr κ)) (init : List (List Bool)) :
    List (List Bool) :=
  prog.foldl (fun bs ins => bs ++ [F ins.kind (ins.srcs.map (BitSrc.eval x bs))]) init

/-- The blocks computed by a program on input `x`. -/
def progBlocks (x : List Bool) (prog : List (GInstr κ)) : List (List Bool) :=
  progRun F x prog []

/-- Running two instruction lists in sequence is running their concatenation. -/
theorem progRun_append (x : List Bool) (p q : List (GInstr κ)) (init : List (List Bool)) :
    progRun F x (p ++ q) init = progRun F x q (progRun F x p init) := by
  simp [progRun, List.foldl_append]

/-- Running a program appends one block per instruction. -/
@[simp] theorem length_progRun (x : List Bool) (prog : List (GInstr κ))
    (init : List (List Bool)) : (progRun F x prog init).length = init.length + prog.length := by
  induction prog generalizing init with
  | nil => simp [progRun]
  | cons g gs ih =>
    have := ih (init ++ [F g.kind (g.srcs.map (BitSrc.eval x init))])
    simp only [progRun, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

/-- Running more instructions only appends blocks. -/
theorem progRun_getD_of_lt (x : List Bool) (prog : List (GInstr κ)) (init : List (List Bool))
    {i : ℕ} (hi : i < init.length) : (progRun F x prog init).getD i [] = init.getD i [] := by
  induction prog generalizing init with
  | nil => rfl
  | cons g gs ih =>
    have := ih (init ++ [F g.kind (g.srcs.map (BitSrc.eval x init))]) (by simp; omega)
    simp only [progRun, List.foldl_cons] at this ⊢
    rw [this, List.getD_append _ _ _ _ hi]

/-- The well-formedness of a program on `n` inputs with blocks of width `w`: every
source is valid for its instruction. -/
def ProgWF (n w : ℕ) (prog : List (GInstr κ)) : Prop :=
  ∀ (i : ℕ) (h : i < prog.length), ∀ s ∈ (prog[i]).srcs, s.Valid n w i

/-- A valid source reads the same value from any two block lists agreeing below `i`. -/
theorem BitSrc.eval_congr (x : List Bool) {n w i : ℕ} {s : BitSrc} (hs : s.Valid n w i)
    {bs bs' : List (List Bool)} (h : ∀ i' < i, bs.getD i' [] = bs'.getD i' []) :
    s.eval x bs = s.eval x bs' := by
  cases s with
  | input k => rfl
  | const b => rfl
  | block i' j => simp only [BitSrc.eval, h i' hs.1]

/-- **The defining equation of a block**: block `i` of a well-formed program is `F` of its
kind applied to its sources, read in the full list of blocks.

**Proof sketch.** Split the program at instruction `i`: block `i` is `F` of its sources
read in the blocks of the first `i` instructions, which agree with the full list below
`i` (running more instructions only appends), and a valid source reads only below `i`
(`BoolCircuit.BitSrc.eval_congr`). -/
theorem progBlocks_getD {n w : ℕ} (x : List Bool) (prog : List (GInstr κ))
    (hwf : ProgWF n w prog) {i : ℕ} (hi : i < prog.length) :
    (progBlocks F x prog).getD i [] =
      F (prog[i]).kind ((prog[i]).srcs.map (BitSrc.eval x (progBlocks F x prog))) := by
  have hsplit : prog = prog.take i ++ (prog[i] :: prog.drop (i + 1)) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have hlen : (prog.take i).length = i := List.length_take_of_le hi.le
  set pre := progRun F x (prog.take i) [] with hpre
  have hpl : pre.length = i := by simp [hpre, hlen]
  have hfull : progBlocks F x prog = progRun F x (prog.drop (i + 1))
      (pre ++ [F (prog[i]).kind ((prog[i]).srcs.map (BitSrc.eval x pre))]) := by
    rw [progBlocks]; conv_lhs => rw [hsplit]
    rw [progRun_append]; rfl
  have hagree : ∀ i' < i, pre.getD i' [] = (progBlocks F x prog).getD i' [] := by
    intro i' hi'
    rw [hfull, progRun_getD_of_lt F x (prog.drop (i + 1)) _ (by simp; omega),
      List.getD_append _ _ _ _ (by omega)]
  rw [hfull, progRun_getD_of_lt F x (prog.drop (i + 1)) _ (by simp; omega),
    List.getD_append_right _ _ _ _ (by omega), hpl, Nat.sub_self, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro s hs
  have := BitSrc.eval_congr x (hwf i hi s hs) hagree
  rwa [hfull] at this

end Semantics

/-! ## Compilation -/

section Compile

variable {κ : Type} (m w : ℕ) (F : κ → List Bool → List Bool)

/-- The gadgets of kind `κ₀`: gadget `j < w` computes bit `j` of `F κ₀` on `m` bits. -/
noncomputable def kindGadgets (κ₀ : κ) : List (DAGCircuit m) :=
  (List.range w).map fun j => gadget fun v => (F κ₀ (List.ofFn v)).getD j false

/-- There is one gadget per output bit of a kind. -/
@[simp] theorem length_kindGadgets (κ₀ : κ) : (kindGadgets m w F κ₀).length = w := by
  simp [kindGadgets]

/-- The number of gates an instruction of kind `κ₀` compiles to. -/
noncomputable def kindWidth (κ₀ : κ) : ℕ := embedWidth (kindGadgets m w F κ₀)

/-- The first vertex of the gates compiled from instruction `i`. -/
noncomputable def progBase (n : ℕ) (prog : List (GInstr κ)) (i : ℕ) : ℕ :=
  n + 2 + ((prog.take i).map fun ins => kindWidth m w F ins.kind).sum

/-- Later instructions start at later vertices. -/
theorem progBase_mono (n : ℕ) (prog : List (GInstr κ)) {i i' : ℕ} (h : i ≤ i') :
    progBase m w F n prog i ≤ progBase m w F n prog i' := by
  unfold progBase
  have : ((prog.take i).map fun ins => kindWidth m w F ins.kind).sum ≤
      ((prog.take i').map fun ins => kindWidth m w F ins.kind).sum := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [List.take_add, List.map_append, List.sum_append]
    exact Nat.le_add_right _ _
  omega

/-- Instruction `i + 1` starts right after the gates of instruction `i`. -/
theorem progBase_succ (n : ℕ) (prog : List (GInstr κ)) {i : ℕ} (hi : i < prog.length) :
    progBase m w F n prog (i + 1) = progBase m w F n prog i + kindWidth m w F (prog[i]).kind := by
  simp only [progBase, List.take_succ, List.map_append, List.sum_append,
    List.getElem?_eq_getElem hi, Option.toList_some, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]
  omega

variable [Inhabited κ]

/-- The default instruction (used only out of range). -/
instance : Inhabited (GInstr κ) := ⟨⟨default, []⟩⟩

/-- The vertex holding bit `j` of block `i`. -/
noncomputable def progVertex (n : ℕ) (prog : List (GInstr κ)) (i j : ℕ) : ℕ :=
  progBase m w F n prog i + embedOffset (kindGadgets m w F (prog.getD i default).kind) j

/-- The vertex read for a source of instruction `i` (invalid sources read the constant `0`
vertex, so that compilation never needs a well-formedness proof). -/
noncomputable def srcVertex (n : ℕ) (prog : List (GInstr κ)) (i : ℕ) (s : BitSrc) : ℕ :=
  if s.Valid n w i then
    match s with
    | .input k => k
    | .const b => if b then n + 1 else n
    | .block i' j => progVertex m w F n prog i' j
  else n

/-- The source vertices of instruction `i`, padded or truncated to exactly `m` (padding
reads the constant `0` vertex; a well-formed program with `m` sources per instruction
needs no padding). -/
noncomputable def srcVertices (n : ℕ) (prog : List (GInstr κ)) (i : ℕ) : List ℕ :=
  ((prog.getD i default).srcs.map (srcVertex m w F n prog i) ++ List.replicate m n).take m

/-- Every instruction reads exactly `m` source vertices. -/
@[simp] theorem length_srcVertices (n : ℕ) (prog : List (GInstr κ)) (i : ℕ) :
    (srcVertices m w F n prog i).length = m := by
  simp [srcVertices]

/-- The gates compiled from the first `i` instructions, after the two constant gates
(vertex `n` is `0`, vertex `n + 1` is `1`). -/
noncomputable def progGates (n : ℕ) (prog : List (GInstr κ)) : ℕ → List DAGGate
  | 0 => [constGate false, constGate true]
  | i + 1 => progGates n prog i ++
      embedAll (kindGadgets m w F (prog.getD i default).kind)
        (srcVertices m w F n prog i) (progBase m w F n prog i)

/-- The compiled gates of the first `i` instructions end at `progBase i`. -/
theorem length_progGates (n : ℕ) (prog : List (GInstr κ)) {i : ℕ} (hi : i ≤ prog.length) :
    n + (progGates m w F n prog i).length = progBase m w F n prog i := by
  induction i with
  | zero => simp [progGates, progBase]
  | succ i ih =>
    rw [progGates, List.length_append, ← Nat.add_assoc, ih (by omega), length_embedAll]
    simp only [progBase, List.take_succ, List.map_append, List.sum_append, List.getElem?_eq_getElem
      (show i < prog.length by omega), Option.toList_some, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero, List.getD_eq_getElem _ _
      (show i < prog.length by omega), kindWidth]
    omega

/-- The output vertices of instruction `i` lie before instruction `i + 1`. -/
theorem progVertex_lt (n : ℕ) (prog : List (GInstr κ)) {i j : ℕ} (hi : i < prog.length)
    (hj : j < w) : progVertex m w F n prog i j < progBase m w F n prog (i + 1) := by
  have := embedOffset_lt (kindGadgets m w F (prog[i]).kind) (j := j) (by simpa using hj)
  rw [progBase_succ m w F n prog hi, progVertex, List.getD_eq_getElem _ _ hi, kindWidth]
  omega

/-- A source vertex of instruction `i` lies before instruction `i`. -/
theorem srcVertex_lt (n : ℕ) (prog : List (GInstr κ)) {i : ℕ} (hi : i ≤ prog.length)
    (s : BitSrc) : srcVertex m w F n prog i s < progBase m w F n prog i := by
  have h2 : n + 2 ≤ progBase m w F n prog i := by simp [progBase]
  unfold srcVertex
  split_ifs with hv
  · cases s with
    | input k => simp only [BitSrc.Valid] at hv; dsimp only; omega
    | const b => cases b <;> dsimp only <;> simp <;> omega
    | block i' j =>
      obtain ⟨hi', hj⟩ := hv
      exact (progVertex_lt m w F n prog (by omega) hj).trans_le
        (progBase_mono m w F n prog (by omega))
  · omega

/-- All source vertices of instruction `i` lie before instruction `i`. -/
theorem srcVertices_lt (n : ℕ) (prog : List (GInstr κ)) {i : ℕ} (hi : i ≤ prog.length) :
    ∀ a ∈ srcVertices m w F n prog i, a < progBase m w F n prog i := by
  intro a ha
  have h2 : n + 2 ≤ progBase m w F n prog i := by simp [progBase]
  have ha' := List.mem_of_mem_take ha
  rcases List.mem_append.mp ha' with ha' | ha'
  · obtain ⟨s, -, rfl⟩ := List.mem_map.mp ha'
    exact srcVertex_lt m w F n prog hi s
  · rw [(List.mem_replicate.mp ha').2]; omega

/-- The compiled gates read only earlier vertices. -/
theorem gatesAcyclic_progGates (n : ℕ) (prog : List (GInstr κ)) {i : ℕ}
    (hi : i ≤ prog.length) : GatesAcyclic n (progGates m w F n prog i) := by
  induction i with
  | zero =>
    intro i' hi' a ha
    simp only [progGates, List.length_cons, List.length_nil] at hi'
    rcases (by omega : i' = 0 ∨ i' = 1) with rfl | rfl <;> simp [progGates, constGate] at ha
  | succ i ih =>
    refine (ih (by omega)).append ?_
    rw [length_progGates m w F n prog (by omega)]
    exact gatesAcyclic_embedAll _ _ _ (length_srcVertices m w F n prog i)
      (srcVertices_lt m w F n prog (by omega))

/-- The compiled gates are well formed with fan-in at most two. -/
theorem faninTwo_progGates (n : ℕ) (prog : List (GInstr κ)) (i : ℕ) :
    ∀ g ∈ progGates m w F n prog i,
      g.args.Nodup ∧ (g.kind = .not → g.args.length = 1) ∧ g.args.length ≤ 2 := by
  induction i with
  | zero =>
    intro g hg
    simp only [progGates, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl <;> simp [constGate]
  | succ i ih =>
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact ih g hg
    · refine faninTwo_embedAll _ (fun D hD => ?_) _ _ g hg
      simp only [kindGadgets, List.mem_map, List.mem_range] at hD
      obtain ⟨j, -, rfl⟩ := hD
      exact gadget_isFaninTwo _

/-- **Compilation is correct.**  After the gates of the first `i` instructions of a
well-formed program with `m` sources per instruction, the vertex values hold the input,
the two constants, and bit `j < w` of every block `i' < i`.

**Proof sketch.** Induction on `i`.  The gates of instruction `i` only append vertices.
Its source vertices hold the values of its sources (inputs, constants, and earlier
blocks, by the induction hypothesis), so its gadget `j` outputs bit `j` of `F` of its
kind on them, which is bit `j` of block `i` by its defining equation
(`BoolCircuit.progBlocks_getD`). -/
theorem progGates_values {n : ℕ} (x : Fin n → Bool) (prog : List (GInstr κ))
    (hwf : ProgWF n w prog) (hm : ∀ ins ∈ prog, ins.srcs.length = m) {i : ℕ}
    (hi : i ≤ prog.length) :
    (∀ k : Fin n, (runWith DAGGate.eval (progGates m w F n prog i) (List.ofFn x)).getD k false
      = x k) ∧
    (runWith DAGGate.eval (progGates m w F n prog i) (List.ofFn x)).getD n false = false ∧
    (runWith DAGGate.eval (progGates m w F n prog i) (List.ofFn x)).getD (n + 1) false = true ∧
    ∀ i' < i, ∀ j < w,
      (runWith DAGGate.eval (progGates m w F n prog i) (List.ofFn x)).getD
          (progVertex m w F n prog i' j) false =
        ((progBlocks F (List.ofFn x) prog).getD i' []).getD j false := by
  induction i with
  | zero =>
    have h0 : runWith DAGGate.eval (progGates m w F n prog 0) (List.ofFn x) =
        List.ofFn x ++ [false, true] := by
      have := runWith_eval_constGates [false, true] (List.ofFn x)
      simpa [progGates] using this
    rw [h0]
    refine ⟨fun k => ?_, by simp, by simp, fun i' hi' => absurd hi' (Nat.not_lt_zero _)⟩
    rw [List.getD_append _ _ _ _ (by simp)]
    simp
  | succ i ih =>
    obtain ⟨hin, hF, hT, hblk⟩ := ih (by omega)
    have hip : i < prog.length := by omega
    set V := runWith DAGGate.eval (progGates m w F n prog i) (List.ofFn x) with hV
    have hlenV : V.length = progBase m w F n prog i := by
      rw [hV, length_runWith, List.length_ofFn, length_progGates m w F n prog (by omega)]
    have hstep : runWith DAGGate.eval (progGates m w F n prog (i + 1)) (List.ofFn x) =
        runWith DAGGate.eval (embedAll (kindGadgets m w F (prog.getD i default).kind)
          (srcVertices m w F n prog i) V.length) V := by
      rw [progGates, runWith_append, ← hV, hlenV]
    have hold : ∀ v < progBase m w F n prog i,
        (runWith DAGGate.eval (progGates m w F n prog (i + 1)) (List.ofFn x)).getD v false =
          V.getD v false := by
      intro v hv
      rw [hstep]
      exact runWith_getD_of_lt _ _ _ (by omega) _
    have h2 : n + 2 ≤ progBase m w F n prog i := by simp [progBase]
    -- the source vertices carry the source values
    have hsrc : (srcVertices m w F n prog i).map (fun v => V.getD v false) =
        (prog[i]).srcs.map (BitSrc.eval (List.ofFn x) (progBlocks F (List.ofFn x) prog)) := by
      rw [srcVertices, List.getD_eq_getElem _ _ hip,
        List.take_left' (by simp [hm _ (List.getElem_mem hip)]), List.map_map]
      apply List.map_congr_left
      intro s hs
      have hv := hwf i hip s hs
      simp only [Function.comp, srcVertex, if_pos hv]
      cases s with
      | input k =>
        simp only [BitSrc.Valid] at hv
        have := hin ⟨k, hv⟩
        simp only at this
        rw [this, BitSrc.eval, List.getD_eq_getElem _ _ (by simpa using hv), List.getElem_ofFn]
      | const b =>
        cases b
        · simpa only [Bool.false_eq_true, if_false, BitSrc.eval] using hF
        · simpa only [if_true, BitSrc.eval] using hT
      | block i' j => exact hblk i' hv.1 j hv.2
    have hnew : ∀ j < w,
        (runWith DAGGate.eval (progGates m w F n prog (i + 1)) (List.ofFn x)).getD
          (progVertex m w F n prog i j) false =
          ((progBlocks F (List.ofFn x) prog).getD i []).getD j false := by
      intro j hj
      rw [hstep, progVertex, ← hlenV,
        runWith_embedAll_getD _ _ (length_srcVertices m w F n prog i) V
          (fun a ha => hlenV ▸ srcVertices_lt m w F n prog (by omega) a ha) (by simpa using hj)]
      simp only [kindGadgets, List.getElem_map, List.getElem_range, gadget_eval]
      rw [ofFn_getD_eq_map _ (length_srcVertices m w F n prog i) (fun v => V.getD v false), hsrc,
        progBlocks_getD F _ prog hwf hip, List.getD_eq_getElem _ _ hip]
    refine ⟨fun k => ?_, ?_, ?_, fun i' hi' j hj => ?_⟩
    · rw [hold k (by have := k.isLt; omega)]; exact hin k
    · rw [hold n (by omega)]; exact hF
    · rw [hold (n + 1) (by omega)]; exact hT
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi' | rfl
      · rw [hold _ ((progVertex_lt m w F n prog (by omega) hj).trans_le
          (progBase_mono m w F n prog (by omega)))]
        exact hblk i' hi' j hj
      · exact hnew j hj

/-- **The compiled circuit** of a program on `n` inputs, with output bit `j` of block `i`
(the constant `0` if out of range). -/
noncomputable def progCircuit (n : ℕ) (prog : List (GInstr κ)) (i j : ℕ) : DAGCircuit n where
  gates := progGates m w F n prog prog.length
  output := if i < prog.length ∧ j < w then progVertex m w F n prog i j else n
  args_lt := gatesAcyclic_progGates m w F n prog le_rfl
  output_lt := by
    have hb := length_progGates m w F n prog (le_refl prog.length)
    have h2 : n + 2 ≤ progBase m w F n prog prog.length := by simp [progBase]
    split_ifs with h
    · have := (progVertex_lt m w F n prog h.1 h.2).trans_le
        (progBase_mono m w F n prog h.1)
      omega
    · omega

/-- The compiled circuit outputs bit `j` of block `i` of the program. -/
theorem progCircuit_eval {n : ℕ} (prog : List (GInstr κ)) (hwf : ProgWF n w prog)
    (hm : ∀ ins ∈ prog, ins.srcs.length = m) {i j : ℕ} (hi : i < prog.length) (hj : j < w)
    (x : Fin n → Bool) :
    (progCircuit m w F n prog i j).eval x =
      ((progBlocks F (List.ofFn x) prog).getD i []).getD j false := by
  simp only [DAGCircuit.eval, DAGCircuit.values, progCircuit, if_pos (And.intro hi hj)]
  exact (progGates_values m w F x prog hwf hm le_rfl).2.2.2 i hi j hj

/-- The compiled circuit has fan-in at most two. -/
theorem progCircuit_isFaninTwo (n : ℕ) (prog : List (GInstr κ)) (i j : ℕ) :
    (progCircuit m w F n prog i j).IsFaninTwo := by
  have key := faninTwo_progGates m w F n prog prog.length
  exact ⟨fun g hg => ⟨(key g hg).1, (key g hg).2.1⟩, fun g hg => (key g hg).2.2⟩

/-- The size of the compiled circuit: `n + 2` plus the gate counts of the instructions'
kinds. -/
theorem progCircuit_size (n : ℕ) (prog : List (GInstr κ)) (i j : ℕ) :
    (progCircuit m w F n prog i j).size = progBase m w F n prog prog.length := by
  simp only [DAGCircuit.size, progCircuit]
  exact length_progGates m w F n prog le_rfl

/-- With finitely many kinds, the compiled circuit has at most
`n + 2 + |prog| · W` vertices, `W` the largest gate count of a kind. -/
theorem progCircuit_size_le [Fintype κ] (n : ℕ) (prog : List (GInstr κ)) (i j : ℕ) :
    (progCircuit m w F n prog i j).size ≤
      n + 2 + prog.length * Finset.univ.sup (kindWidth m w F) := by
  rw [progCircuit_size, progBase, List.take_length]
  have : (prog.map fun ins => kindWidth m w F ins.kind).sum ≤
      prog.length * Finset.univ.sup (kindWidth m w F) := by
    clear i j
    induction prog with
    | nil => simp
    | cons ins prog ih =>
      have := Finset.le_sup (f := kindWidth m w F) (Finset.mem_univ ins.kind)
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      omega
  omega

end Compile

end BoolCircuit
