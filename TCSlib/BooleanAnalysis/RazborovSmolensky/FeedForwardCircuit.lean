/-
Copyright (c) 2026 Yichuan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichuan Wang
-/
import Mathlib.Computability.MyhillNerode
import Mathlib.Data.Set.Card
import TCSlib.BooleanAnalysis.Switching.Circuit

universe u v

namespace ACP

/-- A single operation in a feedforward circuit. -/
structure GateOp (α : Type u) where
  ι : Type u
  func : (ι → α) → α

/-- A gate together with the wiring of its inputs. -/
structure Gate (α : Type u) (domain : Type v) where
  op : GateOp α
  inputs : op.ι → domain

/-- A layered feedforward circuit. Layer `0` is the input layer. -/
structure FeedForward (α : Type u) (inp : Type v) (out : Type v) where
  depth : ℕ
  nodes : Fin (depth + 1) → Type v
  gates : (d : Fin depth) → nodes d.succ → Gate α (nodes d.castSucc)
  nodes_zero : nodes 0 = inp
  nodes_last : nodes (Fin.last depth) = out

namespace FeedForward

attribute [simp] FeedForward.nodes_zero FeedForward.nodes_last

variable {α : Type u} {inp out : Type v}

/-- The identity gate. -/
abbrev GateOp.id (α : Type u) : GateOp α where
  ι := PUnit
  func x := x PUnit.unit

/-- Evaluate a single gate from the values on the previous layer. -/
def Gate.eval {domain : Type v} (g : Gate α domain) (xs : domain → α) : α :=
  g.op.func (xs ∘ g.inputs)

variable (F : FeedForward α inp out)

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

end FeedForward

/-!
## Conversion between FeedForward and BoolCircuit.Circuit

A `BoolCircuit.Circuit n` is **tree-shaped** (fanout ≤ 1 — each wire is used by exactly one
gate downstream).  A `FeedForward Bool (Fin n) out` is a **layered DAG** that permits
fanout > 1.  The two directions of conversion have different costs:

* **`FeedForward.toCircuit`** (DAG → tree, "tree-unrolling"): every node whose output
  is consumed by `k` downstream gates is duplicated `k` times.  If every gate has at most
  `f` input wires, the resulting tree has at most `(f + 1) ^ F.depth` nodes — an
  exponential blowup in depth.

* **`BoolCircuit.Circuit.toFeedForward`** (tree → DAG): a tree is already a DAG with
  fanout ≤ 1, so the embedding is faithful.  The FeedForward circuit has the same depth
  and its size is at most `C.size * C.depth` after inserting identity wires to pad
  shorter branches of an unbalanced tree to a uniform depth.
-/

section CircuitConversion

open BoolCircuit

variable {n : ℕ} {out : Type}

/-- Every circuit has at least one node. -/
theorem _root_.BoolCircuit.Circuit.one_le_size (C : Circuit n) : 1 ≤ C.size := by
  cases C with
  | lit l => simp [Circuit.size]
  | node isAnd cs => simp [Circuit.size]

/-! ### FeedForward Bool → BoolCircuit.Circuit (tree-unrolling) -/

/-- Predicate: every gate in `F` computes AND (when `isAnd d v = true`) or OR (when
    `isAnd d v = false`) of its inputs, as enumerated by `gfin`.  This is the gate
    restriction that makes a FeedForward circuit convertible into a `BoolCircuit.Circuit`. -/
def FeedForward.IsAndOrGate
    (F : FeedForward Bool (Fin n) out)
    (isAnd : ∀ d : Fin F.depth, F.nodes d.succ → Bool)
    (gfin : ∀ (d : Fin F.depth) (v : F.nodes d.succ), Fintype (F.gates d v).op.ι) : Prop :=
  ∀ (d : Fin F.depth) (v : F.nodes d.succ) (xs : (F.gates d v).op.ι → Bool),
    haveI := gfin d v
    (F.gates d v).op.func xs =
      if isAnd d v then Finset.univ.val.toList.foldr (fun i acc => xs i && acc) true
      else Finset.univ.val.toList.foldr (fun i acc => xs i || acc) false

/-- Tree-unrolling: recursively expand node `v` at layer `m` into a `BoolCircuit.Circuit n`.
    Nodes used by multiple downstream gates are **duplicated**.
    * Layer-0 nodes (input variables) become positive literals.
    * Internal nodes become `Circuit.node` with one child subtree per input wire. -/
private noncomputable def nodeToCircuit
    (F : FeedForward Bool (Fin n) out)
    (isAnd : ∀ d : Fin F.depth, F.nodes d.succ → Bool)
    (gfin : ∀ (d : Fin F.depth) (v : F.nodes d.succ), Fintype (F.gates d v).op.ι) :
    ∀ (m : ℕ) (hm : m < F.depth + 1), F.nodes ⟨m, hm⟩ → Circuit n :=
  Nat.recAux
    (fun _ v => .lit ⟨F.nodes_zero ▸ v, true⟩)
    (fun m ih hm v =>
      have hm' : m < F.depth := Nat.lt_of_succ_lt_succ hm
      haveI : Fintype (F.gates ⟨m, hm'⟩ v).op.ι := gfin ⟨m, hm'⟩ v
      .node (isAnd ⟨m, hm'⟩ v)
        (Finset.univ.val.toList.map fun i => ih _ ((F.gates ⟨m, hm'⟩ v).inputs i)))

/-- Tree-unrolled circuit evaluates identically to the original feedforward circuit. -/
theorem nodeToCircuit_eval
    (F : FeedForward Bool (Fin n) out)
    (isAnd : ∀ d : Fin F.depth, F.nodes d.succ → Bool)
    (gfin : ∀ (d : Fin F.depth) (v : F.nodes d.succ), Fintype (F.gates d v).op.ι)
    (hcorrect : F.IsAndOrGate isAnd gfin)
    (m : ℕ) (hm : m < F.depth + 1) (v : F.nodes ⟨m, hm⟩) (x : Fin n → Bool) :
    (nodeToCircuit F isAnd gfin m hm v).eval x = F.evalNode v x := by
  induction m with
  | zero =>
    -- nodeToCircuit 0 = .lit ... by Nat.recAux_zero
    have h1 : nodeToCircuit F isAnd gfin 0 hm v = .lit ⟨F.nodes_zero ▸ v, true⟩ := by
      unfold nodeToCircuit; simp
    -- evalNode at d=0 = x (nodes_zero ▸ v) by Nat.recAux_zero
    have h2 : F.evalNode (d := ⟨0, hm⟩) v x = x (F.nodes_zero ▸ v) := by
      unfold FeedForward.evalNode; simp
    rw [h1, h2]; simp [Circuit.eval, Lit.eval]
  | succ m ih =>
    let hm' : m < F.depth := Nat.lt_of_succ_lt_succ hm
    let hm_lt : m < F.depth + 1 := Nat.lt_succ_of_lt hm'
    letI : Fintype (F.gates ⟨m, hm'⟩ v).op.ι := gfin ⟨m, hm'⟩ v
    -- nodeToCircuit (m+1) = .node ... by Nat.recAux_succ
    have h_node : nodeToCircuit F isAnd gfin (m + 1) hm v =
        .node (isAnd ⟨m, hm'⟩ v)
          (Finset.univ.val.toList.map fun i =>
            nodeToCircuit F isAnd gfin m hm_lt ((F.gates ⟨m, hm'⟩ v).inputs i)) := by
      unfold nodeToCircuit; rw [Nat.recAux_succ]
    -- evalNode at m+1 = Gate.eval (gate at m) ∘ evalNode at m
    have h_eval : F.evalNode (d := ⟨m + 1, hm⟩) v x =
        (F.gates ⟨m, hm'⟩ v).op.func
          (fun i => F.evalNode (d := ⟨m, hm_lt⟩) ((F.gates ⟨m, hm'⟩ v).inputs i) x) := by
      unfold FeedForward.evalNode; simp only []; rw [Nat.recAux_succ]
      simp only [FeedForward.Gate.eval]; rfl
    -- IH: each child's eval equals the corresponding evalNode
    have h_ih : ∀ i, (nodeToCircuit F isAnd gfin m hm_lt ((F.gates ⟨m, hm'⟩ v).inputs i)).eval x =
        F.evalNode (d := ⟨m, hm_lt⟩) ((F.gates ⟨m, hm'⟩ v).inputs i) x :=
      fun i => ih hm_lt ((F.gates ⟨m, hm'⟩ v).inputs i)
    rw [h_node, h_eval, hcorrect ⟨m, hm'⟩ v]
    cases isAnd ⟨m, hm'⟩ v <;> simp [Circuit.eval, List.foldr_map, h_ih]

/-
Size bound: tree-unrolled circuit at depth `m` has at most `(k + 1) ^ m` nodes,
    where `k` bounds the fanin (number of input wires) of every gate.
-/
theorem nodeToCircuit_size_le
    (F : FeedForward Bool (Fin n) out)
    (isAnd : ∀ d : Fin F.depth, F.nodes d.succ → Bool)
    (gfin : ∀ (d : Fin F.depth) (v : F.nodes d.succ), Fintype (F.gates d v).op.ι)
    {k : ℕ} (hk : ∀ (d : Fin F.depth) (v : F.nodes d.succ),
        Fintype.card (F.gates d v).op.ι ≤ k)
    (m : ℕ) (hm : m < F.depth + 1) (v : F.nodes ⟨m, hm⟩) :
    (nodeToCircuit F isAnd gfin m hm v).size ≤ (k + 1) ^ m := by
  revert hm v;
  induction' m with m ih;
  · intro hm v; unfold nodeToCircuit; simp +decide [ Circuit.size ] ;
  · intro hm v
    have h_node : (nodeToCircuit F isAnd gfin (m + 1) hm v).size = 1 + (Finset.univ.val.toList.map fun i => (nodeToCircuit F isAnd gfin m (Nat.lt_of_succ_lt hm) ((F.gates ⟨m, Nat.lt_of_succ_lt_succ hm⟩ v).inputs i)).size).foldr (fun c acc => c + acc) 0 := by
      unfold nodeToCircuit; simp +decide [ Nat.recAux ] ;
      unfold Circuit.size; simp +decide [ List.foldr_map ] ;
      congr! 2;
      congr! 2;
      exact Circuit.size.eq_def _;
    have h_foldr : ∀ (L : List ℕ), (∀ c ∈ L, c ≤ (k + 1) ^ m) → L.foldr (fun c acc => c + acc) 0 ≤ L.length * (k + 1) ^ m := by
      intro L hL; induction L <;> simp_all +decide [ Nat.succ_mul ] ;
      grind;
    have := h_foldr ( List.map ( fun i => ( nodeToCircuit F isAnd gfin m ( Nat.lt_of_succ_lt hm ) ( ( F.gates ⟨ m, Nat.lt_of_succ_lt_succ hm ⟩ v ).inputs i ) ).size ) Finset.univ.val.toList ) ?_ <;> simp_all +decide [ pow_succ' ];
    · nlinarith [ hk ⟨ m, Nat.lt_of_succ_lt_succ hm ⟩ v, pow_pos ( Nat.succ_pos k ) m ];

namespace FeedForward

/-- Convert a FeedForward AND/OR circuit to a `BoolCircuit.Circuit` by tree-unrolling.
    The output node `o : out` selects which single-bit output to expand.
    Shared nodes are duplicated; the resulting circuit has size ≤ `(k + 1) ^ F.depth`
    when every gate has at most `k` input wires. -/
noncomputable def toCircuit
    (F : FeedForward Bool (Fin n) out)
    (isAnd : ∀ d : Fin F.depth, F.nodes d.succ → Bool)
    (gfin : ∀ (d : Fin F.depth) (v : F.nodes d.succ), Fintype (F.gates d v).op.ι)
    (o : out) : Circuit n :=
  nodeToCircuit F isAnd gfin F.depth (Fin.last F.depth).isLt (F.nodes_last.symm.rec o)

theorem toCircuit_eval
    (F : FeedForward Bool (Fin n) out)
    (isAnd : ∀ d : Fin F.depth, F.nodes d.succ → Bool)
    (gfin : ∀ (d : Fin F.depth) (v : F.nodes d.succ), Fintype (F.gates d v).op.ι)
    (hcorrect : F.IsAndOrGate isAnd gfin)
    (o : out) (x : Fin n → Bool) :
    (F.toCircuit isAnd gfin o).eval x = F.eval x o := by
  simp only [toCircuit, eval]
  exact nodeToCircuit_eval F isAnd gfin hcorrect _ _ _ x

theorem toCircuit_size_le
    (F : FeedForward Bool (Fin n) out)
    (isAnd : ∀ d : Fin F.depth, F.nodes d.succ → Bool)
    (gfin : ∀ (d : Fin F.depth) (v : F.nodes d.succ), Fintype (F.gates d v).op.ι)
    {k : ℕ} (hk : ∀ (d : Fin F.depth) (v : F.nodes d.succ),
        Fintype.card (F.gates d v).op.ι ≤ k)
    (o : out) :
    (F.toCircuit isAnd gfin o).size ≤ (k + 1) ^ F.depth :=
  nodeToCircuit_size_le F isAnd gfin hk F.depth _ _

end FeedForward

/-! ### BoolCircuit.Circuit → FeedForward Bool (tree embedding) -/

/-- Embed a `BoolCircuit.Circuit n` as a `FeedForward Bool (Fin n) Unit`.
    The circuit is already tree-shaped (fanout ≤ 1), so no duplication occurs.
    Shorter branches of an unbalanced tree are padded with identity wires so that
    all paths reach depth `C.depth`.  The resulting feedforward circuit has size
    at most `C.size * C.depth`. --/

-- Layer 0 is the input layer (Fin n); all other layers carry Unit (single output wire).
-- The gate at layer 0 computes C.eval from all inputs at once; gates at layers 1..depth
-- are identity wires that pass the single Bool value upward unchanged.
noncomputable def _root_.BoolCircuit.Circuit.toFeedForward (C : Circuit n) : FeedForward Bool (Fin n) Unit where
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
      { op := FeedForward.GateOp.id Bool
        inputs := fun _ => Eq.mpr hdom () }
  nodes_zero := if_pos rfl
  nodes_last := by
    show (if (Fin.last (C.depth + 1)).val = 0 then Fin n else Unit) = Unit
    rw [Fin.val_last]; exact if_neg (Nat.succ_ne_zero C.depth)

/-
Every non-input layer node of `C.toFeedForward` evaluates to `C.eval x`.
    Layer 1 applies the `C.eval` gate to the inputs; higher layers are identity wires.
-/
private theorem Circuit.toFeedForward_evalNode_const (C : Circuit n) (x : Fin n → Bool)
    (m : ℕ) (hm : m < C.depth + 1 + 1) (hpos : 0 < m)
    (v : C.toFeedForward.nodes ⟨m, hm⟩) :
    C.toFeedForward.evalNode (d := ⟨m, hm⟩) v x = C.eval x := by
  rcases m with ( _ | m ) <;> simp_all +decide;
  induction' m with m ih;
  · congr! 1;
  · convert ih ( Nat.lt_of_succ_lt hm ) _ using 1

/-- The embedded feedforward circuit evaluates identically to the original `Circuit`.
    Proof: evalNode traces backward through identity gates at layers 1..depth, then
    the layer-0 C.eval gate computes C.eval xs from the input layer. -/
theorem Circuit.toFeedForward_eval (C : Circuit n) (x : Fin n → Bool) :
    C.toFeedForward.eval₁ x = C.eval x := by
  convert Circuit.toFeedForward_evalNode_const C x ( C.toFeedForward.depth ) ( by simp +decide [ Circuit.toFeedForward ] ) ( by simp +decide [ Circuit.toFeedForward ] ) _

/-- The embedding uses one extra layer for the input, so depth is C.depth + 1. -/
theorem Circuit.toFeedForward_depth (C : Circuit n) :
    C.toFeedForward.depth = C.depth + 1 := rfl

/-
The embedded feedforward circuit has size ≤ C.size * (C.depth + 1).
    Its size equals C.depth + 1 (one Unit gate per layer), and C.size ≥ 1.
-/
theorem Circuit.toFeedForward_size_le (C : Circuit n) :
    C.toFeedForward.size ≤ C.size * (C.depth + 1) := by
  refine' le_trans _ ( Nat.le_mul_of_pos_left _ <| BoolCircuit.Circuit.one_le_size C );
  unfold FeedForward.size;
  rw [ show C.toFeedForward.nodes = fun d => if d.val = 0 then Fin n else Unit from funext fun x => by cases x; rfl ] ; simp +decide;
  exact Nat.le_refl C.toFeedForward.depth

end CircuitConversion

end ACP
