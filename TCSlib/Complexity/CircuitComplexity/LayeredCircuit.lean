/-
Copyright (c) 2026 Yichuan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichuan Wang
-/
import Mathlib.Computability.MyhillNerode
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Fin
import TCSlib.Complexity.CircuitComplexity.Basic

/-!
# Layered circuits

Layered DAG circuits over an arbitrary alphabet (formerly `FeedForward`): `GateOp`/`Gate`/`LayeredCircuit`,
evaluation (`evalNode`, `eval`, `eval₁`), the `size`/`Finite`/`onlyUsesGates`
measures, and `stdGateOps` — the standard unbounded fan-in gate set that
`Language.InLayeredSIZE` and `P/poly` are defined over.  The second half relates the
DAG model to the tree-shaped `BoolCircuit.TreeCircuit` in both directions:
tree-unrolling (`LayeredCircuit.toTreeCircuit`, exponential in depth) and the
semantic wrapper `TreeCircuit.toLayeredWrapper`, which packages a tree's *evaluation*
as a single unrestricted first-layer gate — not a gate-level embedding; see
its docstring.  The gate-level conversions, through the book's `DAGCircuit`, are in
`LayeredDAG.lean` (`TreeCircuit.toLayered`, `DAGCircuit.toLayered`, `LayeredCircuit.toDAG`).

Written for the Razborov–Smolensky development
(`BooleanAnalysis/RazborovSmolensky/`) and relocated here as the shared
circuit model.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (Circuit basics: §6.1–6.2.)
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

namespace BoolCircuit

/-- A single operation in a feedforward circuit. -/
structure GateOp (α : Type u) where
  ι : Type u
  func : (ι → α) → α

/-- A gate together with the wiring of its inputs. -/
structure Gate (α : Type u) (domain : Type v) where
  op : GateOp α
  inputs : op.ι → domain

/-- A layered feedforward circuit. Layer `0` is the input layer. -/
structure LayeredCircuit (α : Type u) (inp : Type v) (out : Type v) where
  depth : ℕ
  nodes : Fin (depth + 1) → Type v
  gates : (d : Fin depth) → nodes d.succ → Gate α (nodes d.castSucc)
  nodes_zero : nodes 0 = inp
  nodes_last : nodes (Fin.last depth) = out

namespace LayeredCircuit

attribute [simp] LayeredCircuit.nodes_zero LayeredCircuit.nodes_last

variable {α : Type u} {inp out : Type v}

/-- The identity gate. -/
abbrev GateOp.id (α : Type u) : GateOp α where
  ι := PUnit
  func x := x PUnit.unit

/-- Evaluate a single gate from the values on the previous layer. -/
def Gate.eval {domain : Type v} (g : Gate α domain) (xs : domain → α) : α :=
  g.op.func (xs ∘ g.inputs)

variable (F : LayeredCircuit α inp out)

/-- Evaluate a node of a feedforward circuit. -/
def evalNode {d : Fin (F.depth + 1)} (node : F.nodes d) (xs : inp → α) : α :=
  let ⟨d, hd⟩ := d
  Nat.recAux
    (fun _ node' => xs (F.nodes_zero ▸ node'))
    (fun n ih hd node₀ =>
      Gate.eval (F.gates ⟨n, Nat.succ_lt_succ_iff.mp hd⟩ node₀) (ih _))
    d hd node

/-- Evaluate a circuit on an input. -/
def eval (xs : inp → α) : out → α :=
  fun o => F.evalNode (d := Fin.last F.depth) (F.nodes_last.symm.rec o) xs

/-- Evaluate a circuit with a unique output node. -/
def eval₁ [Unique out] (xs : inp → α) : α :=
  F.eval xs default

/-- The total number of non-input gates. -/
noncomputable def size : ℕ :=
  Nat.card (@Sigma (Fin F.depth) (fun d => F.nodes d.succ))

/-- Every layer is finite. -/
protected abbrev Finite : Prop :=
  ∀ i, Finite (F.nodes i)

/-- Every gate operation belongs to the given gate set. -/
def onlyUsesGates (S : Set (GateOp α)) : Prop :=
  ∀ d u, (F.gates d u).op ∈ S

end LayeredCircuit

/-! ### The standard gate set -/

/-- The standard unbounded fan-in gate set — identity, NOT, and unbounded AND.
This is the basis `Language.InLayeredSIZE` and `P/poly` are defined over; it is also
the gate set of plain `AC⁰` circuits, and `RazborovSmolensky.ACp_GateOps`
extends it with `MOD p` gates. -/
def stdGateOps : Set (GateOp (Fin 2)) :=
  {LayeredCircuit.GateOp.id (Fin 2),
   ⟨Fin 1, fun x ↦ 1 - x 0⟩} ∪
  ⋃ n, {⟨Fin n, fun x ↦ ∏ i, x i⟩}

/-!
## Conversion between FeedForward and BoolCircuit.Circuit

A `BoolCircuit.TreeCircuit n` is **tree-shaped** (fanout ≤ 1 — each wire is used by exactly one
gate downstream).  A `LayeredCircuit Bool (Fin n) out` is a **layered DAG** that permits
fanout > 1.  The two directions of conversion have different costs:

* **`LayeredCircuit.toTreeCircuit`** (DAG → tree, "tree-unrolling"): every node whose output
  is consumed by `k` downstream gates is duplicated `k` times.  If every gate has at most
  `f` input wires, the resulting tree has at most `(f + 1) ^ F.depth` nodes — an
  exponential blowup in depth.

* **`BoolCircuit.TreeCircuit.toLayeredWrapper`** (tree → semantic wrapper): packages the
  tree's *evaluation* as a single unrestricted layer-0 gate `⟨Fin n, C.eval⟩`
  followed by `C.depth` identity layers, so `size = depth = C.depth + 1`.  No
  source gate is copied, no branch is padded, and no gate basis is preserved in
  general — see the declaration's docstring.
-/

section CircuitConversion

variable {n : ℕ} {out : Type}

/-! ### FeedForward Bool → BoolCircuit.Circuit (tree-unrolling) -/

/-- Predicate: every gate in `F` computes AND (when `isAnd d v = true`) or OR (when
    `isAnd d v = false`) of its inputs, as enumerated by `gfin`.  This is the gate
    restriction that makes a FeedForward circuit convertible into a `BoolCircuit.TreeCircuit`. -/
def LayeredCircuit.IsAndOrGate
    (F : LayeredCircuit Bool (Fin n) out)
    (isAnd : ∀ d : Fin F.depth, F.nodes d.succ → Bool)
    (gfin : ∀ (d : Fin F.depth) (v : F.nodes d.succ), Fintype (F.gates d v).op.ι) : Prop :=
  ∀ (d : Fin F.depth) (v : F.nodes d.succ) (xs : (F.gates d v).op.ι → Bool),
    haveI := gfin d v
    (F.gates d v).op.func xs =
      if isAnd d v then Finset.univ.val.toList.foldr (fun i acc => xs i && acc) true
      else Finset.univ.val.toList.foldr (fun i acc => xs i || acc) false

/-- Tree-unrolling: recursively expand node `v` at layer `m` into a `BoolCircuit.TreeCircuit n`.
    Nodes used by multiple downstream gates are **duplicated**.
    * Layer-0 nodes (input variables) become positive literals.
    * Internal nodes become `TreeCircuit.node` with one child subtree per input wire. -/
private noncomputable def nodeToTreeCircuit
    (F : LayeredCircuit Bool (Fin n) out)
    (isAnd : ∀ d : Fin F.depth, F.nodes d.succ → Bool)
    (gfin : ∀ (d : Fin F.depth) (v : F.nodes d.succ), Fintype (F.gates d v).op.ι) :
    ∀ (m : ℕ) (hm : m < F.depth + 1), F.nodes ⟨m, hm⟩ → TreeCircuit n :=
  Nat.recAux
    (fun _ v => .lit ⟨F.nodes_zero ▸ v, true⟩)
    (fun m ih hm v =>
      have hm' : m < F.depth := Nat.lt_of_succ_lt_succ hm
      haveI : Fintype (F.gates ⟨m, hm'⟩ v).op.ι := gfin ⟨m, hm'⟩ v
      .node (isAnd ⟨m, hm'⟩ v)
        (Finset.univ.val.toList.map fun i => ih _ ((F.gates ⟨m, hm'⟩ v).inputs i)))

/-- Tree-unrolled circuit evaluates identically to the original feedforward circuit. -/
theorem nodeToTreeCircuit_eval
    (F : LayeredCircuit Bool (Fin n) out)
    (isAnd : ∀ d : Fin F.depth, F.nodes d.succ → Bool)
    (gfin : ∀ (d : Fin F.depth) (v : F.nodes d.succ), Fintype (F.gates d v).op.ι)
    (hcorrect : F.IsAndOrGate isAnd gfin)
    (m : ℕ) (hm : m < F.depth + 1) (v : F.nodes ⟨m, hm⟩) (x : Fin n → Bool) :
    (nodeToTreeCircuit F isAnd gfin m hm v).eval x = F.evalNode v x := by
  induction m with
  | zero =>
    -- nodeToCircuit 0 = .lit ... by Nat.recAux_zero
    have h1 : nodeToTreeCircuit F isAnd gfin 0 hm v = .lit ⟨F.nodes_zero ▸ v, true⟩ := by
      unfold nodeToTreeCircuit; simp
    -- evalNode at d=0 = x (nodes_zero ▸ v) by Nat.recAux_zero
    have h2 : F.evalNode (d := ⟨0, hm⟩) v x = x (F.nodes_zero ▸ v) := by
      unfold LayeredCircuit.evalNode; simp
    rw [h1, h2]; simp [TreeCircuit.eval, Lit.eval]
  | succ m ih =>
    let hm' : m < F.depth := Nat.lt_of_succ_lt_succ hm
    let hm_lt : m < F.depth + 1 := Nat.lt_succ_of_lt hm'
    letI : Fintype (F.gates ⟨m, hm'⟩ v).op.ι := gfin ⟨m, hm'⟩ v
    -- nodeToCircuit (m+1) = .node ... by Nat.recAux_succ
    have h_node : nodeToTreeCircuit F isAnd gfin (m + 1) hm v =
        .node (isAnd ⟨m, hm'⟩ v)
          (Finset.univ.val.toList.map fun i =>
            nodeToTreeCircuit F isAnd gfin m hm_lt ((F.gates ⟨m, hm'⟩ v).inputs i)) := by
      unfold nodeToTreeCircuit; rw [Nat.recAux_succ]
    -- evalNode at m+1 = Gate.eval (gate at m) ∘ evalNode at m
    have h_eval : F.evalNode (d := ⟨m + 1, hm⟩) v x =
        (F.gates ⟨m, hm'⟩ v).op.func
          (fun i => F.evalNode (d := ⟨m, hm_lt⟩) ((F.gates ⟨m, hm'⟩ v).inputs i) x) := by
      unfold LayeredCircuit.evalNode; simp only []; rw [Nat.recAux_succ]
      simp only [LayeredCircuit.Gate.eval]; rfl
    -- IH: each child's eval equals the corresponding evalNode
    have h_ih : ∀ i, (nodeToTreeCircuit F isAnd gfin m hm_lt ((F.gates ⟨m, hm'⟩ v).inputs i)).eval x =
        F.evalNode (d := ⟨m, hm_lt⟩) ((F.gates ⟨m, hm'⟩ v).inputs i) x :=
      fun i => ih hm_lt ((F.gates ⟨m, hm'⟩ v).inputs i)
    rw [h_node, h_eval, hcorrect ⟨m, hm'⟩ v]
    cases isAnd ⟨m, hm'⟩ v <;> simp [TreeCircuit.eval, List.foldr_map, h_ih]

/-
Size bound: tree-unrolled circuit at depth `m` has at most `(k + 1) ^ m` nodes,
    where `k` bounds the fanin (number of input wires) of every gate.
-/
theorem nodeToTreeCircuit_size_le
    (F : LayeredCircuit Bool (Fin n) out)
    (isAnd : ∀ d : Fin F.depth, F.nodes d.succ → Bool)
    (gfin : ∀ (d : Fin F.depth) (v : F.nodes d.succ), Fintype (F.gates d v).op.ι)
    {k : ℕ} (hk : ∀ (d : Fin F.depth) (v : F.nodes d.succ),
        Fintype.card (F.gates d v).op.ι ≤ k)
    (m : ℕ) (hm : m < F.depth + 1) (v : F.nodes ⟨m, hm⟩) :
    (nodeToTreeCircuit F isAnd gfin m hm v).size ≤ (k + 1) ^ m := by
  revert hm v;
  induction' m with m ih;
  · intro hm v; unfold nodeToTreeCircuit; simp +decide [ TreeCircuit.size ] ;
  · intro hm v
    have h_node : (nodeToTreeCircuit F isAnd gfin (m + 1) hm v).size = 1 + (Finset.univ.val.toList.map fun i => (nodeToTreeCircuit F isAnd gfin m (Nat.lt_of_succ_lt hm) ((F.gates ⟨m, Nat.lt_of_succ_lt_succ hm⟩ v).inputs i)).size).foldr (fun c acc => c + acc) 0 := by
      unfold nodeToTreeCircuit; simp +decide [ Nat.recAux ] ;
      unfold TreeCircuit.size; simp +decide [ List.foldr_map ] ;
      congr! 2;
      congr! 2;
      exact TreeCircuit.size.eq_def _;
    have h_foldr : ∀ (L : List ℕ), (∀ c ∈ L, c ≤ (k + 1) ^ m) → L.foldr (fun c acc => c + acc) 0 ≤ L.length * (k + 1) ^ m := by
      intro L hL; induction L <;> simp_all +decide [ Nat.succ_mul ] ;
      grind;
    have := h_foldr ( List.map ( fun i => ( nodeToTreeCircuit F isAnd gfin m ( Nat.lt_of_succ_lt hm ) ( ( F.gates ⟨ m, Nat.lt_of_succ_lt_succ hm ⟩ v ).inputs i ) ).size ) Finset.univ.val.toList ) ?_ <;> simp_all +decide [ pow_succ' ];
    · nlinarith [ hk ⟨ m, Nat.lt_of_succ_lt_succ hm ⟩ v, pow_pos ( Nat.succ_pos k ) m ];

namespace LayeredCircuit

/-- Convert a FeedForward AND/OR circuit to a `BoolCircuit.TreeCircuit` by tree-unrolling.
    The output node `o : out` selects which single-bit output to expand.
    Shared nodes are duplicated; the resulting circuit has size ≤ `(k + 1) ^ F.depth`
    when every gate has at most `k` input wires. -/
noncomputable def toTreeCircuit
    (F : LayeredCircuit Bool (Fin n) out)
    (isAnd : ∀ d : Fin F.depth, F.nodes d.succ → Bool)
    (gfin : ∀ (d : Fin F.depth) (v : F.nodes d.succ), Fintype (F.gates d v).op.ι)
    (o : out) : TreeCircuit n :=
  nodeToTreeCircuit F isAnd gfin F.depth (Fin.last F.depth).isLt (F.nodes_last.symm.rec o)

/-- Tree-unrolling preserves evaluation: `F.toTreeCircuit isAnd gfin o` computes
`F.eval x o`. -/
theorem toTreeCircuit_eval
    (F : LayeredCircuit Bool (Fin n) out)
    (isAnd : ∀ d : Fin F.depth, F.nodes d.succ → Bool)
    (gfin : ∀ (d : Fin F.depth) (v : F.nodes d.succ), Fintype (F.gates d v).op.ι)
    (hcorrect : F.IsAndOrGate isAnd gfin)
    (o : out) (x : Fin n → Bool) :
    (F.toTreeCircuit isAnd gfin o).eval x = F.eval x o := by
  simp only [toTreeCircuit, eval]
  exact nodeToTreeCircuit_eval F isAnd gfin hcorrect _ _ _ x

/-- The tree-unrolled circuit has size at most `(k + 1) ^ F.depth` when every
gate reads at most `k` wires. -/
theorem toTreeCircuit_size_le
    (F : LayeredCircuit Bool (Fin n) out)
    (isAnd : ∀ d : Fin F.depth, F.nodes d.succ → Bool)
    (gfin : ∀ (d : Fin F.depth) (v : F.nodes d.succ), Fintype (F.gates d v).op.ι)
    {k : ℕ} (hk : ∀ (d : Fin F.depth) (v : F.nodes d.succ),
        Fintype.card (F.gates d v).op.ι ≤ k)
    (o : out) :
    (F.toTreeCircuit isAnd gfin o).size ≤ (k + 1) ^ F.depth :=
  nodeToTreeCircuit_size_le F isAnd gfin hk F.depth _ _

end LayeredCircuit

/-! ### BoolCircuit.Circuit → FeedForward Bool (semantic wrapper) -/

-- Layer 0 is the input layer (Fin n); all other layers carry Unit (single output wire).
-- The gate at layer 0 computes C.eval from all inputs at once; gates at layers 1..depth
-- are identity wires that pass the single Bool value upward unchanged.
/-- Package a `BoolCircuit.TreeCircuit n` as a `LayeredCircuit Bool (Fin n) Unit` — a
    **semantic wrapper, not a gate-level embedding**: the single layer-0 gate is
    the unrestricted operation `⟨Fin n, C.eval⟩` and every later layer is one
    identity wire, so `size = depth = C.depth + 1` whatever `C.size` is.  The
    source gates are not embedded, no branch is padded, and the first gate is in
    general **not** in `stdGateOps`, so this map supplies **no general basis
    guarantee** and cannot serve as a general machine-to-standard-circuit
    construction; the gate-level conversion is `TreeCircuit.toLayered` (`LayeredDAG.lean`).
    (Individual wrapped gates may happen to be standard: a single positive
    literal `C : TreeCircuit 1` transports to `andGateOp 1`.)  Only evaluation is preserved
    (`TreeCircuit.toLayeredWrapper_eval`). -/
noncomputable def _root_.BoolCircuit.TreeCircuit.toLayeredWrapper (C : TreeCircuit n) : LayeredCircuit Bool (Fin n) Unit where
  depth := C.depth + 1
  nodes d := if d.val = 0 then Fin n else Unit
  gates d _ :=
    if h : d.val = 0 then
      -- Layer 0 → 1: compute C.eval from the input layer
      let h' : d.castSucc.val = 0 := h  -- castSucc preserves val
      let hdom : (if d.castSucc.val = 0 then Fin n else Unit) = Fin n := if_pos h'
      { op := { ι := Fin n, func := C.eval }
        inputs := Eq.mpr hdom }
    else
      -- Layer d > 0 → d+1: identity wire
      let h' : d.castSucc.val ≠ 0 := h  -- castSucc preserves val
      let hdom : (if d.castSucc.val = 0 then Fin n else Unit) = Unit := if_neg h'
      { op := LayeredCircuit.GateOp.id Bool
        inputs := fun _ => Eq.mpr hdom () }
  nodes_zero := if_pos rfl
  nodes_last := by
    show (if (Fin.last (C.depth + 1)).val = 0 then Fin n else Unit) = Unit
    rw [Fin.val_last]; exact if_neg (Nat.succ_ne_zero C.depth)

/-
Every non-input layer node of `C.toLayeredWrapper` evaluates to `C.eval x`.
    Layer 1 applies the `C.eval` gate to the inputs; higher layers are identity wires.
-/
private theorem TreeCircuit.toLayeredWrapper_evalNode_const (C : TreeCircuit n) (x : Fin n → Bool)
    (m : ℕ) (hm : m < C.depth + 1 + 1) (hpos : 0 < m)
    (v : C.toLayeredWrapper.nodes ⟨m, hm⟩) :
    C.toLayeredWrapper.evalNode (d := ⟨m, hm⟩) v x = C.eval x := by
  rcases m with ( _ | m ) <;> simp_all +decide;
  induction' m with m ih;
  · congr! 1;
  · convert ih ( Nat.lt_of_succ_lt hm ) _ using 1

/-- The wrapped feedforward circuit evaluates identically to the original `TreeCircuit`.
    Proof: evalNode traces backward through identity gates at layers 1..depth, then
    the layer-0 C.eval gate computes C.eval xs from the input layer. -/
theorem TreeCircuit.toLayeredWrapper_eval (C : TreeCircuit n) (x : Fin n → Bool) :
    C.toLayeredWrapper.eval₁ x = C.eval x := by
  convert TreeCircuit.toLayeredWrapper_evalNode_const C x ( C.toLayeredWrapper.depth ) ( by simp +decide [ TreeCircuit.toLayeredWrapper ] ) ( by simp +decide [ TreeCircuit.toLayeredWrapper ] ) _

/-- The wrapper prepends one evaluation layer and keeps one identity layer per
source depth unit, so depth is `C.depth + 1`. -/
theorem TreeCircuit.toLayeredWrapper_depth (C : TreeCircuit n) :
    C.toLayeredWrapper.depth = C.depth + 1 := rfl

/-
The wrapped feedforward circuit has size ≤ C.size * (C.depth + 1).
    Its size equals C.depth + 1 (one Unit gate per layer), and C.size ≥ 1.
-/
theorem TreeCircuit.toLayeredWrapper_size_le (C : TreeCircuit n) :
    C.toLayeredWrapper.size ≤ C.size * (C.depth + 1) := by
  refine' le_trans _ ( Nat.le_mul_of_pos_left _ <| BoolCircuit.TreeCircuit.one_le_size C );
  unfold LayeredCircuit.size;
  rw [ show C.toLayeredWrapper.nodes = fun d => if d.val = 0 then Fin n else Unit from funext fun x => by cases x; rfl ] ; simp +decide;
  exact Nat.le_refl C.toLayeredWrapper.depth

end CircuitConversion

end BoolCircuit
