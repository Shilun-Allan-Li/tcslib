/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.HardWire
import TCSlib.Complexity.CircuitComplexity.DAGFanin
import TCSlib.Complexity.CircuitComplexity.Universal

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Constant-size gadgets wired into a circuit

The circuit-building step of the proof of [AB09, Thm 6.6] (p. 110): "`zᵢ` is computed
from `x`, `z_{i−1}` and `z_{i₁}, …, z_{i_k}` by a constant-size circuit", and the
compositions of such circuits.  This file supplies the generic mechanism, independent of
Turing machines:

* a **gadget** for an arbitrary Boolean function `f` on `m` bits: a fan-in-two
  `BoolCircuit.DAGCircuit m` computing `f`, obtained from the DNF circuit of
  [AB09, Claim 2.13] (`BoolCircuit.universalCircuit`), compiled to a DAG
  (`TreeCircuit.toDAG`) and binarized (`DAGCircuit.binarize`).  Its size depends only on
  `m` (and `f`), not on where it is used;
* **embedding** a gadget into a growing gate list: its input `i` is wired to an arbitrary
  existing vertex `srcs[i]` (sources may repeat), its gates are renumbered after the
  existing vertices, and one copy gate puts its output at a known vertex;
* embedding a whole **list of gadgets** sharing the same sources (a multi-output
  constant-size circuit, [AB09, p. 114: "the obvious generalization of Def 6.1"]), with
  the output of gadget `j` at the fixed offset `BoolCircuit.embedOffset Ds j`.

## Main definitions

* `BoolCircuit.gadget f` — a fan-in-two circuit computing `f`.
* `BoolCircuit.embedGates D srcs L` — the gates of `D` rewired to read `srcs` and placed
  after `L` existing vertices, followed by a copy of its output.
* `BoolCircuit.embedAll Ds srcs L`, `BoolCircuit.embedWidth Ds`,
  `BoolCircuit.embedOffset Ds j` — the same for a list of gadgets, its total number of
  gates, and the vertex offset of the `j`-th output.

## Main results

* `BoolCircuit.gadget_eval`, `BoolCircuit.gadget_isFaninTwo`.
* `BoolCircuit.runWith_embedAll_getD` — after running the embedded gadgets, the vertex
  `L + embedOffset Ds j` holds `Ds[j]` evaluated on the source values.
* `BoolCircuit.gatesAcyclic_embedAll`, `BoolCircuit.faninTwo_embedAll` — the embedded
  gates read only earlier vertices and keep fan-in two and well-formedness (sources that
  coincide are merged, so no gate reads a vertex twice).

## Divergences from [AB09]

* The book's "constant-size circuit" is any circuit for the finite function; we fix the
  DNF construction for definiteness.  The constant it yields is exponential in the number
  of source bits, which is irrelevant for the asymptotics (it is a constant of the
  machine), but it is far from the best possible.
* Each embedded gadget costs one extra copy gate (an `∧` of fan-in one) so that its output
  sits at a vertex number that does not depend on whether the gadget's output is one of its
  own inputs.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, proof of Theorem 6.6, pp. 109–110; Claim 2.13.)
-/

namespace BoolCircuit

/-! ## Gadgets -/

/-- A fan-in-two circuit computing an arbitrary Boolean function `f` on `m` bits: the DNF
circuit of [AB09, Claim 2.13] compiled to a DAG and binarized.  Its size is a function of
`f` alone (bounded in terms of `m`), the "constant-size circuit" of the proof of
[AB09, Thm 6.6]. -/
noncomputable def gadget {m : ℕ} (f : (Fin m → Bool) → Bool) : DAGCircuit m :=
  (universalCircuit f).toDAG.binarize (TreeCircuit.toDAG_isWellFormed _)

/-- The gadget for `f` computes `f`. -/
theorem gadget_eval {m : ℕ} (f : (Fin m → Bool) → Bool) (x : Fin m → Bool) :
    (gadget f).eval x = f x := by
  rw [gadget, DAGCircuit.binarize_eval, TreeCircuit.toDAG_eval, universalCircuit_eval]

/-- The gadget for `f` has fan-in at most two. -/
theorem gadget_isFaninTwo {m : ℕ} (f : (Fin m → Bool) → Bool) : (gadget f).IsFaninTwo :=
  DAGCircuit.binarize_isFaninTwo _ _

/-! ## Merging repeated arguments -/

/-- The gate `g` with repeated input vertices merged. -/
def DAGGate.dedupArgs (g : DAGGate) : DAGGate :=
  ⟨g.kind, g.args.dedup⟩

/-- Merging repeated inputs does not change a gate's value (`∧`, `∨` and `¬` of a
conjunction are all insensitive to repetitions). -/
theorem DAGGate.eval_dedupArgs (g : DAGGate) (vals : List Bool) :
    g.dedupArgs.eval vals = g.eval vals := by
  have hall : (g.args.dedup.all fun a => vals.getD a false) =
      g.args.all fun a => vals.getD a false := by
    rw [Bool.eq_iff_iff]; simp [List.all_eq_true, List.mem_dedup]
  have hany : (g.args.dedup.any fun a => vals.getD a false) =
      g.args.any fun a => vals.getD a false := by
    rw [Bool.eq_iff_iff]; simp [List.any_eq_true, List.mem_dedup]
  rcases g with ⟨k, args⟩
  cases k <;> simp only [DAGGate.dedupArgs, DAGGate.eval] at hall hany ⊢ <;>
    simp only [hall, hany]

/-- Running gates with merged arguments gives the same vertex values. -/
theorem runWith_eval_map_dedupArgs (gs : List DAGGate) (init : List Bool) :
    runWith DAGGate.eval (gs.map DAGGate.dedupArgs) init = runWith DAGGate.eval gs init := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih => rw [List.map_cons, runWith_cons, runWith_cons, ih, DAGGate.eval_dedupArgs]

/-- The input of a gadget whose input `i` reads vertex `l[i]` is the list of values of
`l`. -/
theorem ofFn_getD_eq_map {m : ℕ} (l : List ℕ) (hl : l.length = m) (f : ℕ → Bool) :
    List.ofFn (fun i : Fin m => f (l.getD i 0)) = l.map f := by
  subst hl
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

/-- A Boolean read through a list of vertex names is the entry of the mapped list (the
entrywise form of `ofFn_getD_eq_map`). -/
theorem getD_map_getD {l : List ℕ} {f : ℕ → Bool} {i : ℕ} (hi : i < l.length) :
    f (l.getD i 0) = (l.map f).getD i false := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by simpa using hi),
    List.getElem_map]

/-! ## Embedding one gadget -/

/-- The renaming used to embed a gadget with `m` inputs after `L` existing vertices: input
`i` goes to the source vertex `srcs[i]`, gate vertex `m + i` to the new vertex `L + i`. -/
def embedMap (m L : ℕ) (srcs : List ℕ) (v : ℕ) : ℕ :=
  if v < m then srcs.getD v 0 else L + (v - m)

/-- The gates of the gadget `D` wired to read the vertices `srcs` and placed after `L`
existing vertices, followed by one copy gate holding `D`'s output; that output is then
at vertex `L + D.gates.length`. -/
def embedGates {m : ℕ} (D : DAGCircuit m) (srcs : List ℕ) (L : ℕ) : List DAGGate :=
  D.gates.map (fun g => (g.remap (embedMap m L srcs)).dedupArgs) ++
    [⟨.and, [embedMap m L srcs D.output]⟩]

/-- An embedded gadget costs its gates plus one copy gate. -/
@[simp] theorem length_embedGates {m : ℕ} (D : DAGCircuit m) (srcs : List ℕ) (L : ℕ) :
    (embedGates D srcs L).length = D.gates.length + 1 := by
  simp [embedGates]

/-- A source read at a gadget input is an existing vertex. -/
theorem getD_src_lt {m L : ℕ} {srcs : List ℕ} (hlen : srcs.length = m)
    (hsrc : ∀ a ∈ srcs, a < L) {v : ℕ} (hv : v < m) : srcs.getD v 0 < L := by
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact hsrc _ (List.getElem_mem _)

/-- The renaming sends the vertices of `D` below the matching new vertices. -/
private theorem embedMap_lt {m L : ℕ} {srcs : List ℕ} (hlen : srcs.length = m)
    (hsrc : ∀ a ∈ srcs, a < L) {v i : ℕ} (hv : v < m + i) : embedMap m L srcs v < L + i := by
  unfold embedMap
  split_ifs with h
  · have := getD_src_lt hlen hsrc h; omega
  · omega

/-- **One embedded gadget.**  Running the embedded gates of `D` after the vertex values
`init` (all sources being existing vertices) puts at vertex `|init| + |D.gates|` the
value of `D` on the source values.

**Proof sketch.** Merging repeated arguments does not change values, and by
`BoolCircuit.runWith_remap_rel` the renamed gates hold, at the image of each vertex of
`D`, that vertex's value on the source values; the copy gate reads the image of `D`'s
output. -/
theorem runWith_embedGates_getD {m : ℕ} (D : DAGCircuit m) (srcs : List ℕ)
    (hlen : srcs.length = m) (init : List Bool) (hsrc : ∀ a ∈ srcs, a < init.length) :
    (runWith DAGGate.eval (embedGates D srcs init.length) init).getD
        (init.length + D.gates.length) false =
      D.eval (fun i => init.getD (srcs.getD i 0) false) := by
  set σ := embedMap m init.length srcs with hσ
  set xD : Fin m → Bool := fun i => init.getD (srcs.getD i 0) false
  have hmap : D.gates.map (fun g => (g.remap σ).dedupArgs) =
      (D.gates.map (DAGGate.remap σ)).map DAGGate.dedupArgs := by simp [List.map_map]
  have key := runWith_remap_rel DAGGate.eval Eq false σ
    (fun g vs vs' h => DAGGate.eval_remap g σ h)
    (L := m) (L' := init.length) (List.ofFn xD) init (by simp) rfl
    (fun v hv => by
      have := embedMap_lt (L := init.length) hlen hsrc (i := 0) (v := v) (by omega)
      simpa using this)
    (fun i => by simp [hσ, embedMap])
    (fun v hv => by
      simp only [hσ, embedMap, if_pos hv]
      rw [List.getD_eq_getElem (List.ofFn xD) false (by simpa using hv), List.getElem_ofFn])
    D.gates D.args_lt
  have hout := key D.output D.output_lt
  rw [embedGates, runWith_append, ← hσ, hmap, runWith_eval_map_dedupArgs, runWith_singleton]
  have hl : (runWith DAGGate.eval (D.gates.map (DAGGate.remap σ)) init).length =
      init.length + D.gates.length := by simp
  rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self, List.getD_cons_zero]
  simp only [DAGGate.eval, List.all_cons, List.all_nil, Bool.and_true]
  rw [hout]
  rfl

/-- The embedded gates of one gadget read only earlier vertices. -/
theorem gatesAcyclic_embedGates {m : ℕ} (D : DAGCircuit m) (srcs : List ℕ) (L : ℕ)
    (hlen : srcs.length = m) (hsrc : ∀ a ∈ srcs, a < L) :
    GatesAcyclic L (embedGates D srcs L) := by
  have hpre : GatesAcyclic L (D.gates.map fun g => (g.remap (embedMap m L srcs)).dedupArgs) := by
    intro i hi a ha
    simp only [List.getElem_map, DAGGate.dedupArgs, DAGGate.remap, List.mem_dedup,
      List.mem_map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    exact embedMap_lt hlen hsrc (D.args_lt i (by simpa using hi) b hb)
  refine hpre.snoc fun a ha => ?_
  simp only [List.mem_singleton] at ha
  subst ha
  simpa using embedMap_lt hlen hsrc (i := D.gates.length) D.output_lt

/-- The embedded gates of a fan-in-two gadget are well formed with fan-in at most two. -/
theorem faninTwo_embedGates {m : ℕ} (D : DAGCircuit m) (hD : D.IsFaninTwo) (srcs : List ℕ)
    (L : ℕ) : ∀ g ∈ embedGates D srcs L,
      g.args.Nodup ∧ (g.kind = .not → g.args.length = 1) ∧ g.args.length ≤ 2 := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
    have hwf := hD.1 g₀ hg₀
    have h2 := hD.2 g₀ hg₀
    have hle : (g₀.args.map (embedMap m L srcs)).dedup.length ≤ g₀.args.length :=
      ((List.dedup_sublist _).length_le).trans (by simp)
    refine ⟨List.nodup_dedup _, fun hk => ?_, ?_⟩
    · have h1 := hwf.2 hk
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h1
      simp [DAGGate.dedupArgs, DAGGate.remap, ha]
    · simp only [DAGGate.dedupArgs, DAGGate.remap]
      omega
  · simp only [List.mem_singleton] at hg
    subst hg
    simp

/-! ## Embedding a list of gadgets -/

/-- Embed the gadgets `Ds` one after another, all reading the same sources `srcs`, after
`L` existing vertices. -/
def embedAll {m : ℕ} : List (DAGCircuit m) → List ℕ → ℕ → List DAGGate
  | [], _, _ => []
  | D :: Ds, srcs, L => embedGates D srcs L ++ embedAll Ds srcs (L + (D.gates.length + 1))

/-- The number of gates `embedAll Ds` emits: one more than each gadget's gate count. -/
def embedWidth {m : ℕ} : List (DAGCircuit m) → ℕ
  | [] => 0
  | D :: Ds => D.gates.length + 1 + embedWidth Ds

/-- The offset, after the existing vertices, of the vertex holding the output of the
`j`-th gadget of `Ds`. -/
def embedOffset {m : ℕ} : List (DAGCircuit m) → ℕ → ℕ
  | [], _ => 0
  | D :: _, 0 => D.gates.length
  | D :: Ds, j + 1 => D.gates.length + 1 + embedOffset Ds j

/-- Embedding a list of gadgets emits `embedWidth` gates. -/
@[simp] theorem length_embedAll {m : ℕ} (Ds : List (DAGCircuit m)) (srcs : List ℕ) (L : ℕ) :
    (embedAll Ds srcs L).length = embedWidth Ds := by
  induction Ds generalizing L with
  | nil => rfl
  | cons D Ds ih => simp [embedAll, embedWidth, ih]

/-- Every output offset lies inside the emitted block. -/
theorem embedOffset_lt {m : ℕ} (Ds : List (DAGCircuit m)) {j : ℕ} (hj : j < Ds.length) :
    embedOffset Ds j < embedWidth Ds := by
  induction Ds generalizing j with
  | nil => simp at hj
  | cons D Ds ih =>
    cases j with
    | zero => simp [embedOffset, embedWidth]; omega
    | succ j =>
      have := ih (j := j) (by simpa using hj)
      simp only [embedOffset, embedWidth]; omega

/-- **A list of embedded gadgets.**  After running `embedAll Ds srcs |init|` from `init`
(all sources being existing vertices), vertex `|init| + embedOffset Ds j` holds the value
of the `j`-th gadget on the source values.

**Proof sketch.** Induction on the list: the first gadget's output is placed by
`BoolCircuit.runWith_embedGates_getD`, and later gadgets see unchanged source values,
since gates only append. -/
theorem runWith_embedAll_getD {m : ℕ} (Ds : List (DAGCircuit m)) (srcs : List ℕ)
    (hlen : srcs.length = m) (init : List Bool) (hsrc : ∀ a ∈ srcs, a < init.length)
    {j : ℕ} (hj : j < Ds.length) :
    (runWith DAGGate.eval (embedAll Ds srcs init.length) init).getD
        (init.length + embedOffset Ds j) false =
      (Ds[j]).eval (fun i => init.getD (srcs.getD i 0) false) := by
  induction Ds generalizing init j with
  | nil => simp at hj
  | cons D Ds ih =>
    rw [embedAll, runWith_append]
    have hl : (runWith DAGGate.eval (embedGates D srcs init.length) init).length =
        init.length + (D.gates.length + 1) := by simp
    cases j with
    | zero =>
      rw [runWith_getD_of_lt _ _ _ (by rw [hl]; simp [embedOffset])]
      exact runWith_embedGates_getD D srcs hlen init hsrc
    | succ j =>
      set init' := runWith DAGGate.eval (embedGates D srcs init.length) init
      have hsrc' : ∀ a ∈ srcs, a < init'.length := fun a ha => by
        have := hsrc a ha; rw [hl]; omega
      have := ih init' hsrc' (j := j) (by simpa using hj)
      rw [hl] at this
      simp only [embedOffset, List.getElem_cons_succ]
      rw [show init.length + (D.gates.length + 1 + embedOffset Ds j) =
        init.length + (D.gates.length + 1) + embedOffset Ds j by omega, this]
      congr 1
      funext i
      exact runWith_getD_of_lt _ _ _ (getD_src_lt hlen hsrc i.isLt) _

/-- The embedded gates of a list of gadgets read only earlier vertices. -/
theorem gatesAcyclic_embedAll {m : ℕ} (Ds : List (DAGCircuit m)) (srcs : List ℕ) (L : ℕ)
    (hlen : srcs.length = m) (hsrc : ∀ a ∈ srcs, a < L) :
    GatesAcyclic L (embedAll Ds srcs L) := by
  induction Ds generalizing L with
  | nil => exact GatesAcyclic.nil
  | cons D Ds ih =>
    rw [embedAll]
    exact (gatesAcyclic_embedGates D srcs L hlen hsrc).append (by
      simpa [Nat.add_assoc] using ih (L + (D.gates.length + 1))
        (fun a ha => by have := hsrc a ha; omega))

/-- The embedded gates of fan-in-two gadgets are well formed with fan-in at most two. -/
theorem faninTwo_embedAll {m : ℕ} (Ds : List (DAGCircuit m)) (hDs : ∀ D ∈ Ds, D.IsFaninTwo)
    (srcs : List ℕ) (L : ℕ) : ∀ g ∈ embedAll Ds srcs L,
      g.args.Nodup ∧ (g.kind = .not → g.args.length = 1) ∧ g.args.length ≤ 2 := by
  induction Ds generalizing L with
  | nil => simp [embedAll]
  | cons D Ds ih =>
    intro g hg
    rw [embedAll] at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact faninTwo_embedGates D (hDs D (by simp)) srcs L g hg
    · exact ih (fun D' hD' => hDs D' (by simp [hD'])) _ g hg
