/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.PSubsetPPolyGadget
import TCSlib.Complexity.CookLevin.Snapshot
import TCSlib.Complexity.ClassP.DTIME

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The tableau circuit of an oblivious machine

The heart of the proof of [AB09, Thm 6.6] (`P ⊆ P/poly`, pp. 109–110): an oblivious machine
`M` running for `T` steps on inputs of length `n` is simulated by a fan-in-two circuit of
size `O(T + n)` that, for `i = 0, 1, …, T`, computes an encoding `zᵢ` of the
`i`-th **snapshot** of the run (state and symbols under the heads,
`Complexity.snapshotAt`) from

* `z_{i−1}`,
* the input bit under the input head at step `i`, and
* for each work tape `τ`, the snapshot `z_{prev}` at the last earlier step at which head
  `τ` visited its current cell (`Complexity.prevVisit`),

by one constant-size circuit per step.  Because `M` is oblivious, which input bit and
which earlier snapshots are read at step `i` depend only on `n` and `i` (the book's
footnote 2), so the wiring is fixed in advance.  The correctness of one step is
"computation is local", already proved in `CookLevin/Snapshot.lean`
(`Complexity.snapshotAt_state_succ`, `snapshotAt_inputSymbol`, `snapshotAt_workSymbol`).

## The circuit, as an explicit function of `(M, n)`

The circuit `Complexity.tableauCircuit M n T` is defined by explicit recursion, not
extracted from an existence proof, so its shape is explicit.  (The uniform families of
[AB09, Remark 6.7, Thms 6.13 and 6.15] are built instead from the non-oblivious
configuration tableau `Complexity.cfgTab`, whose grid wiring needs no oblivious schedule:
`UniformTableau.lean` and `LogspaceTableau.lean`.)  The data:

* **Vertices.**  Inputs `0, …, n − 1`; vertex `n` is the constant `0` and `n + 1` the
  constant `1` (`Complexity.tableauConst`); then one **segment** of exactly
  `Complexity.tableauWidth M` gates per step `t = 0, …, T`, segment `t` starting at
  vertex `Complexity.tableauBase M n t = n + 2 + t · tableauWidth M`.
* **Segment contents.**  Segment `t` is `BoolCircuit.embedAll (tableauGadgets M) srcs _`:
  the *same* list of constant-size gadgets `Complexity.tableauGadgets M` (one per bit of
  the step's output; they depend on `M` only), all reading the source list
  `srcs = Complexity.tableauSources M n t`.  Bit `j` of `z_t` sits at vertex
  `Complexity.tableauVertex M n t j = tableauBase M n t + embedOffset (tableauGadgets M) j`;
  bit `snapWidth M` of segment `t` is the acceptance accumulator.
* **Schedule data.**  `tableauSources M n t` depends on `(M, n, t)` only through the
  oblivious schedule: the input-head position `Complexity.inputPosAt M n t` and the
  last-visit times `Complexity.prevVisit M n t τ` (both defined in
  `CookLevin/Snapshot.lean` from the run on the reference input `0ⁿ`), together with the
  vertex arithmetic above.
* **Output.**  The accumulator of segment `T`.

The size is exactly `n + 2 + (T + 1) · tableauWidth M` (`Complexity.tableauCircuit_size`).

## Main definitions

* `Complexity.snapWidth`, `Complexity.snapEncode`, `Complexity.snapDecode` — a one-hot
  encoding of snapshots by a constant number of bits.
* `Complexity.tableauStep` — the finite function one step computes ([AB09]'s `F`).
* `Complexity.tableauGadgets`, `Complexity.tableauWidth` — its constant-size circuits.
* `Complexity.tableauSources`, `Complexity.tableauVertex`, `Complexity.tableauBase` —
  the wiring.
* `Complexity.tableauCircuit M n T` — the circuit.

## Main results

* `Complexity.tableauCircuit_isFaninTwo`, `Complexity.tableauCircuit_size`.

The correctness of the circuit (`Complexity.tableauCircuit_eval`) and the general tableau
theorem (`Complexity.exists_tableau_circuit`) are in
`CircuitComplexity/PSubsetPPolyTableauCorrect.lean`.

## Divergences from [AB09, Thm 6.6]

* **Multi-tape.**  [AB09] simulates a two-tape oblivious machine; ours has any number `k`
  of work tapes (as produced by `Complexity.oblivious_of_mem_DTIME`), so a step reads `k`
  earlier snapshots.  The step circuit is still of constant size.
* **First visits read blank** (`prevVisit = none`), rather than [AB09]'s convention of
  pointing back to step `1`; the circuit wires constants there.
* **Acceptance.**  Our machines answer by *emitting* a bit on the append-only output tape,
  so the circuit carries one accumulator bit per step ("some step so far emitted `1`")
  instead of reading an accept state off the last snapshot.  For a machine that decides
  `L`, the output tape at the deadline is exactly the answer bit, so this is equivalent.
* **Size `O(T + n)` rather than `O(T)`**: the model counts input vertices in the size.
* **The snapshot encoding is one-hot** and the gadgets are DNF circuits
  (`BoolCircuit.gadget`); both are noncomputable in Lean (they enumerate finite types via
  `Fintype.equivFin` and `Finset.toList`), but they are fixed finite objects depending on
  `M` only.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, Theorem 6.6 and its proof, pp. 109–110;
  §2.3.4 for snapshots.)
-/

namespace Complexity

open Turing BoolCircuit

variable (M : FinTM Bool)

/-! ## Encoding snapshots by bits -/

/-- The number of bits encoding one snapshot: one per possible snapshot (one-hot). -/
def snapWidth : ℕ := Fintype.card (Snapshot M)

/-- The one-hot encoding of a snapshot: bit `j` is `1` iff the snapshot is the `j`-th
one in a fixed enumeration.  A constant-size bit string, as in [AB09, p. 110]. -/
noncomputable def snapEncode (s : Snapshot M) : List Bool :=
  List.ofFn fun j : Fin (snapWidth M) => decide (Fintype.equivFin (Snapshot M) s = j)

/-- A snapshot encoding has `snapWidth M` bits. -/
@[simp] theorem length_snapEncode (s : Snapshot M) : (snapEncode M s).length = snapWidth M := by
  simp [snapEncode]

/-- Distinct snapshots have distinct encodings. -/
theorem snapEncode_injective : Function.Injective (snapEncode M) := by
  intro s s' h
  have hlt : (Fintype.equivFin (Snapshot M) s).val < snapWidth M :=
    (Fintype.equivFin (Snapshot M) s).isLt
  have := congrArg (fun l => l.getD (Fintype.equivFin (Snapshot M) s).val false) h
  simp only [snapEncode] at this
  rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getD_eq_getElem _ _ (by simpa using hlt),
    List.getElem_ofFn, List.getElem_ofFn] at this
  simp only [Fin.eta, decide_true] at this
  exact (Fintype.equivFin (Snapshot M)).injective (of_decide_eq_true this.symm).symm

/-- Decoding: a left inverse of `snapEncode` (arbitrary on non-codewords). -/
noncomputable def snapDecode (l : List Bool) : Snapshot M :=
  Function.invFun (snapEncode M) l

/-- Decoding an encoded snapshot gives it back. -/
@[simp] theorem snapDecode_snapEncode (s : Snapshot M) : snapDecode M (snapEncode M s) = s :=
  Function.leftInverse_invFun (snapEncode_injective M) s

/-! ## One step of the tableau -/

/-- The number of source bits a step reads: the previous snapshot (`snapWidth`), the
"time `0`" flag, the input symbol (present flag and value), for each work tape a present
flag and the last-visit snapshot, and the previous accumulator. -/
def tableauArity : ℕ := snapWidth M + 3 + M.k * (snapWidth M + 1) + 1

/-- **The finite function of one step** ([AB09]'s `F`, eq. (2.3)): from the source bits
of step `t` (see `Complexity.tableauArity` for the layout), the encoding of snapshot `t`
followed by the accumulator bit "some step `< t` emitted `1`".  At time `0` (flag set) the
result is the initial snapshot; otherwise the state steps by `Complexity.stepState`, the
input symbol is the supplied one, and work symbol `τ` is the written-or-kept symbol of the
supplied last-visit snapshot, or blank if there is none. -/
noncomputable def tableauStep (l : List Bool) : List Bool :=
  let B := snapWidth M
  let prev := snapDecode M (l.take B)
  let inSym : Option Bool := if l.getD (B + 1) false then some (l.getD (B + 2) false) else none
  let chunk (τ : Fin M.k) : List Bool := (((l.drop (B + 3)).drop (τ * (B + 1))).take (B + 1))
  let wk : Fin M.k → Option Bool := fun τ =>
    if (chunk τ).headD false then writtenOrKept M (snapDecode M (chunk τ).tail) τ else none
  let acc := l.getD (B + 3 + M.k * (B + 1)) false
  if l.getD B false then
    snapEncode M (some M.tm.q₀, inSym, fun _ => none) ++ [false]
  else
    snapEncode M (stepState M prev, inSym, wk) ++ [acc || decide (emitted M prev = some true)]

/-- The constant-size circuits of one step: gadget `j` computes bit `j` of
`Complexity.tableauStep`.  They depend on `M` only. -/
noncomputable def tableauGadgets : List (DAGCircuit (tableauArity M)) :=
  (List.range (snapWidth M + 1)).map fun j =>
    gadget fun v => (tableauStep M (List.ofFn v)).getD j false

/-- There is one gadget per output bit of a step, `snapWidth M + 1` in all. -/
@[simp] theorem length_tableauGadgets : (tableauGadgets M).length = snapWidth M + 1 := by
  simp [tableauGadgets]

/-- The number of gates of one segment of the tableau: a constant of `M`. -/
noncomputable def tableauWidth : ℕ := embedWidth (tableauGadgets M)

/-! ## The wiring -/

/-- The vertex holding the constant `b`: `n` for `0`, `n + 1` for `1`. -/
def tableauConst (n : ℕ) (b : Bool) : ℕ := if b then n + 1 else n

/-- The first vertex of segment `t`. -/
noncomputable def tableauBase (n t : ℕ) : ℕ := n + 2 + t * tableauWidth M

/-- The vertex holding bit `j` of segment `t`: bit `j < snapWidth M` of the encoding of
snapshot `t`, or (for `j = snapWidth M`) the accumulator after step `t`. -/
noncomputable def tableauVertex (n t j : ℕ) : ℕ :=
  tableauBase M n t + embedOffset (tableauGadgets M) j

/-- The vertices holding the encoding of snapshot `t`. -/
noncomputable def tableauBlock (n t : ℕ) : List ℕ :=
  (List.range (snapWidth M)).map (tableauVertex M n t)

/-- The sources for work tape `τ` at step `t`: the constant `1` followed by the block of
the last-visit snapshot `Complexity.prevVisit M n t τ`, or all constants `0` on a first
visit. -/
noncomputable def tableauTapeSources (n t : ℕ) (τ : Fin M.k) : List ℕ :=
  match prevVisit M n t τ with
  | none => List.replicate (snapWidth M + 1) (tableauConst n false)
  | some s => tableauConst n true :: tableauBlock M n s

/-- **The sources of step `t`** on inputs of length `n`, in the layout of
`Complexity.tableauArity`.  They depend on `(n, t)` only through the oblivious schedule:
the input position `Complexity.inputPosAt M n t` (input vertex `p − 1` when `1 ≤ p ≤ n`,
constants otherwise) and the last-visit times `Complexity.prevVisit M n t τ`.
[AB09, p. 110, footnote 2] -/
noncomputable def tableauSources (n t : ℕ) : List ℕ :=
  (if t = 0 then List.replicate (snapWidth M) (tableauConst n false)
    else tableauBlock M n (t - 1)) ++
  [tableauConst n (decide (t = 0)),
    tableauConst n (decide (1 ≤ inputPosAt M n t ∧ inputPosAt M n t ≤ n)),
    if 1 ≤ inputPosAt M n t ∧ inputPosAt M n t ≤ n then inputPosAt M n t - 1
      else tableauConst n false] ++
  (List.finRange M.k).flatMap (tableauTapeSources M n t) ++
  [if t = 0 then tableauConst n false else tableauVertex M n (t - 1) (snapWidth M)]

/-- The gates of the first `t` segments, after the two constant gates. -/
noncomputable def tableauGates (n : ℕ) : ℕ → List DAGGate
  | 0 => [constGate false, constGate true]
  | t + 1 => tableauGates n t ++
      embedAll (tableauGadgets M) (tableauSources M n t) (tableauBase M n t)

/-! ## Bookkeeping -/

/-- The first `t` segments have `2 + t · tableauWidth M` gates. -/
theorem length_tableauGates (n t : ℕ) :
    (tableauGates M n t).length = 2 + t * tableauWidth M := by
  induction t with
  | zero => simp [tableauGates]
  | succ t ih => simp [tableauGates, ih, tableauWidth]; ring

namespace CfgTableau

/-- A list of equal-length chunks has length `count · chunk length`. -/
theorem length_flatMap_const {α β : Type} (l : List α) (f : α → List β) {c : ℕ}
    (hf : ∀ a, (f a).length = c) : (l.flatMap f).length = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih, hf, Nat.succ_mul]; omega

end CfgTableau

open CfgTableau

/-- The block of a snapshot has `snapWidth M` vertices. -/
@[simp] theorem length_tableauBlock (n t : ℕ) : (tableauBlock M n t).length = snapWidth M := by
  simp [tableauBlock]

/-- The sources for one work tape are `snapWidth M + 1` vertices. -/
theorem length_tableauTapeSources (n t : ℕ) (τ : Fin M.k) :
    (tableauTapeSources M n t τ).length = snapWidth M + 1 := by
  unfold tableauTapeSources; split <;> simp

/-- The sources of a step are exactly `tableauArity M` vertices. -/
theorem length_tableauSources (n t : ℕ) :
    (tableauSources M n t).length = tableauArity M := by
  have hpre : (if t = 0 then List.replicate (snapWidth M) (tableauConst n false)
      else tableauBlock M n (t - 1)).length = snapWidth M := by split <;> simp
  simp only [tableauSources, List.length_append, hpre,
    length_flatMap_const _ _ (length_tableauTapeSources M n t), List.length_finRange,
    tableauArity]
  simp

/-- The vertices of segment `t` lie before segment `t + 1`. -/
theorem tableauVertex_lt (n t : ℕ) {j : ℕ} (hj : j ≤ snapWidth M) :
    tableauVertex M n t j < tableauBase M n (t + 1) := by
  have := embedOffset_lt (tableauGadgets M) (j := j) (by simp; omega)
  simp only [tableauVertex, tableauBase, tableauWidth] at this ⊢
  rw [Nat.succ_mul]; omega

/-- Later segments start at later vertices. -/
theorem tableauBase_mono (n : ℕ) {s t : ℕ} (h : s ≤ t) :
    tableauBase M n s ≤ tableauBase M n t := by
  simp only [tableauBase]
  have := Nat.mul_le_mul_right (tableauWidth M) h
  omega

/-- The constant vertices lie before every segment. -/
theorem tableauConst_lt (n t : ℕ) (b : Bool) : tableauConst n b < tableauBase M n t := by
  simp only [tableauConst, tableauBase]; split <;> omega

/-- The block of snapshot `s` lies before every later segment. -/
theorem tableauBlock_lt (n : ℕ) {s t : ℕ} (h : s < t) :
    ∀ a ∈ tableauBlock M n s, a < tableauBase M n t := by
  intro a ha
  simp only [tableauBlock, List.mem_map, List.mem_range] at ha
  obtain ⟨j, hj, rfl⟩ := ha
  exact (tableauVertex_lt M n s hj.le).trans_le (tableauBase_mono M n h)

/-- A last visit lies strictly in the past. -/
theorem prevVisit_lt {n t s : ℕ} {τ : Fin M.k} (h : prevVisit M n t τ = some s) : s < t := by
  have := List.max?_mem h
  simp only [List.mem_filter, List.mem_range] at this
  exact this.1

/-- All sources of step `t` lie before segment `t`.

**Proof sketch.** Case on the part of the source list: constants and input vertices are
below `n + 2`, the previous block, the accumulator and the last-visit blocks belong to
earlier segments (`Complexity.prevVisit_lt`), and segment `s` ends before segment `t`
for `s < t`. -/
theorem tableauSources_lt (n t : ℕ) :
    ∀ a ∈ tableauSources M n t, a < tableauBase M n t := by
  intro a ha
  simp only [tableauSources, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false,
    List.mem_flatMap, List.mem_finRange, true_and] at ha
  rcases ha with ((ha | ha | ha | ha) | ⟨τ, ha⟩) | ha
  · split at ha
    · rw [(List.mem_replicate.mp ha).2]
      exact tableauConst_lt M n t false
    · exact tableauBlock_lt M n (by omega) a ha
  · subst ha; exact tableauConst_lt M n t _
  · subst ha; exact tableauConst_lt M n t _
  · subst ha
    split
    · have := tableauConst_lt M n t false
      simp only [tableauConst, tableauBase] at this ⊢
      omega
    · exact tableauConst_lt M n t false
  · unfold tableauTapeSources at ha
    split at ha
    · rw [(List.mem_replicate.mp ha).2]
      exact tableauConst_lt M n t false
    · rename_i s hs
      rcases List.mem_cons.mp ha with rfl | ha
      · exact tableauConst_lt M n t true
      · exact tableauBlock_lt M n (prevVisit_lt M hs) a ha
  · subst ha
    split
    · exact tableauConst_lt M n t false
    · exact (tableauVertex_lt M n (t - 1) (le_refl _)).trans_le
        (tableauBase_mono M n (by omega))

/-- The tableau gates read only earlier vertices. -/
theorem gatesAcyclic_tableauGates (n t : ℕ) : GatesAcyclic n (tableauGates M n t) := by
  induction t with
  | zero =>
    intro i hi a ha
    simp only [tableauGates, List.length_cons, List.length_nil] at hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp [tableauGates, constGate] at ha
  | succ t ih =>
    have hL : n + (tableauGates M n t).length = tableauBase M n t := by
      rw [length_tableauGates, tableauBase]; omega
    refine ih.append ?_
    rw [hL]
    exact gatesAcyclic_embedAll _ _ _ (length_tableauSources M n t) (tableauSources_lt M n t)

/-- **The tableau circuit** of `M` for inputs of length `n` and `T` steps: segments
`0, …, T` computing the snapshots `z_0, …, z_T` and the accumulators, with output the
accumulator after step `T`.  [AB09, Thm 6.6, proof] -/
noncomputable def tableauCircuit (n T : ℕ) : DAGCircuit n where
  gates := tableauGates M n (T + 1)
  output := tableauVertex M n T (snapWidth M)
  args_lt := gatesAcyclic_tableauGates M n (T + 1)
  output_lt := by
    have := tableauVertex_lt M n T (le_refl _)
    rw [length_tableauGates]
    simp only [tableauBase] at this
    omega

/-- The tableau circuit has `n + 2 + (T + 1) · tableauWidth M` vertices: `O(T + n)`. -/
theorem tableauCircuit_size (n T : ℕ) :
    (tableauCircuit M n T).size = n + 2 + (T + 1) * tableauWidth M := by
  simp only [DAGCircuit.size, tableauCircuit, length_tableauGates]; omega

/-- The tableau circuit has fan-in at most two. -/
theorem tableauCircuit_isFaninTwo (n T : ℕ) : (tableauCircuit M n T).IsFaninTwo := by
  have key : ∀ t, ∀ g ∈ tableauGates M n t,
      g.args.Nodup ∧ (g.kind = .not → g.args.length = 1) ∧ g.args.length ≤ 2 := by
    intro t
    induction t with
    | zero =>
      intro g hg
      simp only [tableauGates, List.mem_cons, List.mem_nil_iff, or_false] at hg
      rcases hg with rfl | rfl <;> simp [constGate]
    | succ t ih =>
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact ih g hg
      · refine faninTwo_embedAll _ (fun D hD => ?_) _ _ g hg
        simp only [tableauGadgets, List.mem_map, List.mem_range] at hD
        obtain ⟨j, -, rfl⟩ := hD
        exact gadget_isFaninTwo _
  exact ⟨fun g hg => ⟨(key _ g hg).1, (key _ g hg).2.1⟩, fun g hg => (key _ g hg).2.2⟩

end Complexity
