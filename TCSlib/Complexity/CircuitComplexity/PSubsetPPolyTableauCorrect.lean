/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.PSubsetPPolyTableau

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Correctness of the tableau circuit of an oblivious machine

The correctness half of the proof of [AB09, Thm 6.6] (pp. 109–110), for the circuit
`Complexity.tableauCircuit` of `CircuitComplexity/PSubsetPPolyTableau.lean`: by induction
on the step, every segment holds the encoding of the corresponding snapshot, because the
sources of a step carry the encodings of the previous snapshot and of the last-visit
snapshots, and one step of the finite function `Complexity.tableauStep` reproduces the
next snapshot ("computation is local", `CookLevin/Snapshot.lean`).

## Main definitions

* `Complexity.tableauAccepted` — the accumulator value ("some step so far emitted `1`").
* `Complexity.idealSources` — the source bits a step reads when all earlier segments are
  correct.

## Main results

* `Complexity.tableauCircuit_eval` — for oblivious `M`, the circuit outputs `1` on `x`
  iff some step `s < T` of `M`'s run on `x` emits the bit `1`.
* `Complexity.tableauCircuit_eval_of_decidesInTime` — if `M` decides `L` within `T`, the
  circuit for length `n` and budget `T n` decides `L` on length-`n` inputs.
* `Complexity.exists_tableau_circuit` — **the general tableau theorem**: an oblivious `M`
  deciding `L` within `T` has fan-in-two circuits of size `≤ K_M · (T n + n + 1)`.
  [AB09, Thm 6.6, proof]

## Divergences from [AB09, Thm 6.6]

See `CircuitComplexity/PSubsetPPolyTableau.lean` (multi-tape, blank first visits,
acceptance by an emission accumulator, size `O(T + n)`).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, Theorem 6.6 and its proof, pp. 109–110;
  §2.3.4 for snapshots.)
-/

namespace Complexity

open Turing BoolCircuit CfgTableau

variable (M : FinTM Bool)


/-- The output tape of a run is the concatenation of the per-step emissions, each a
function of the snapshot (`Complexity.emitted`). -/
theorem output_runFrom_eq_flatMap (x : List Bool) (t : ℕ) :
    (M.tm.runFrom (M.tm.initCfg x) t).output =
      (List.range t).flatMap fun s => (emitted M (snapshotAt M x s)).toList := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step_output, ih, List.range_succ,
      List.flatMap_append, List.flatMap_singleton]
    congr 2
    unfold MultiTapeTM.outputSymbol emitted snapshotAt
    split <;> simp_all

/-- The accumulator value after step `t`: some step `s < t` of the run on `x` emitted `1`. -/
noncomputable def tableauAccepted (x : List Bool) (t : ℕ) : Bool :=
  decide (∃ s < t, emitted M (snapshotAt M x s) = some true)

/-- The ideal source bits for work tape `τ` at step `t`: `1` and the encoding of the
last-visit snapshot, or all `0` on a first visit. -/
noncomputable def idealTapeBits (x : List Bool) (t : ℕ) (τ : Fin M.k) : List Bool :=
  match prevVisit M x.length t τ with
  | none => List.replicate (snapWidth M + 1) false
  | some s => true :: snapEncode M (snapshotAt M x s)

/-- The ideal source bits of step `t` on input `x`: what the sources of step `t` carry
when the earlier segments are correct. -/
noncomputable def idealSources (x : List Bool) (t : ℕ) : List Bool :=
  (if t = 0 then List.replicate (snapWidth M) false
    else snapEncode M (snapshotAt M x (t - 1))) ++
  [decide (t = 0), (inputBitAt x (inputPosAt M x.length t)).isSome,
    (inputBitAt x (inputPosAt M x.length t)).getD false] ++
  (List.finRange M.k).flatMap (idealTapeBits M x t) ++
  [if t = 0 then false else tableauAccepted M x (t - 1)]

namespace CfgTableau

/-- Reading the `i`-th chunk of a concatenation of equal-length chunks. -/
theorem take_drop_flatMap_append {α β : Type} (l : List α) (g : α → List β) {c : ℕ}
    (hg : ∀ a, (g a).length = c) (rest : List β) {i : ℕ} (hi : i < l.length) :
    (((l.flatMap g) ++ rest).drop (i * c)).take c = g l[i] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    rw [List.flatMap_cons, List.append_assoc]
    cases i with
    | zero => simp [List.take_left' (hg a)]
    | succ i =>
      rw [Nat.succ_mul, Nat.add_comm, ← List.drop_drop, List.drop_left' (hg a)]
      exact ih (by simpa using hi)

end CfgTableau

/-- Decoding the source layout of `Complexity.tableauArity`.

**Proof sketch.** Rewrite the layout as `pre ++ (a :: b :: c :: (F ++ [d]))` and read
each position with the `getD`/`take`/`drop` append lemmas, using `|pre| = snapWidth M` and
`|F| = k (snapWidth M + 1)`. -/
private theorem decode_layout (pre F : List Bool) (a b c d : Bool) (hpre : pre.length = snapWidth M)
    (hF : F.length = M.k * (snapWidth M + 1)) :
    (pre ++ [a, b, c] ++ F ++ [d]).take (snapWidth M) = pre ∧
    (pre ++ [a, b, c] ++ F ++ [d]).getD (snapWidth M) false = a ∧
    (pre ++ [a, b, c] ++ F ++ [d]).getD (snapWidth M + 1) false = b ∧
    (pre ++ [a, b, c] ++ F ++ [d]).getD (snapWidth M + 2) false = c ∧
    (pre ++ [a, b, c] ++ F ++ [d]).drop (snapWidth M + 3) = F ++ [d] ∧
    (pre ++ [a, b, c] ++ F ++ [d]).getD (snapWidth M + 3 + M.k * (snapWidth M + 1)) false
      = d := by
  have e : pre ++ [a, b, c] ++ F ++ [d] = pre ++ (a :: b :: c :: (F ++ [d])) := by simp
  rw [e]
  refine ⟨List.take_left' hpre, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.getD_append_right _ _ _ _ (by omega)]; simp [hpre]
  · rw [List.getD_append_right _ _ _ _ (by omega)]; simp [hpre]
  · rw [List.getD_append_right _ _ _ _ (by omega)]; simp [hpre]
  · rw [show snapWidth M + 3 = pre.length + 3 by omega, ← List.drop_drop, List.drop_left]
    rfl
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hpre, show snapWidth M + 3 + M.k * (snapWidth M + 1) - snapWidth M =
      (F.length + 3) by omega]
    simp

private theorem option_isSome_getD (o : Option Bool) :
    (if o.isSome then some (o.getD false) else none) = o := by
  cases o <;> rfl

/-- **One step is correct** [AB09, eq. (2.3), via `CookLevin/Snapshot.lean`]: on the ideal
source bits of step `t`, the step function returns the encoding of snapshot `t` and the
accumulator after step `t`.

**Proof sketch.** Decode the layout.  At `t = 0` the flag selects the initial snapshot,
which is `Complexity.snapshotAt_zero` with the input symbol at the scheduled position
(`Complexity.snapshotAt_inputSymbol`).  At `t + 1` the previous block decodes to
snapshot `t`; the state is `stepState` of it (`snapshotAt_state_succ`), the input symbol
is the scheduled one, and work symbol `τ` is the written-or-kept symbol of the last-visit
snapshot or blank (`snapshotAt_workSymbol`); the accumulator gains step `t`'s
emission. -/
theorem tableauStep_idealSources {M : FinTM Bool} (hM : M.Oblivious) (x : List Bool)
    (t : ℕ) : tableauStep M (idealSources M x t) =
      snapEncode M (snapshotAt M x t) ++ [tableauAccepted M x t] := by
  have hpre : (if t = 0 then List.replicate (snapWidth M) false
      else snapEncode M (snapshotAt M x (t - 1))).length = snapWidth M := by split <;> simp
  have hlen : ∀ τ, (idealTapeBits M x t τ).length = snapWidth M + 1 := by
    intro τ; unfold idealTapeBits; split <;> simp
  have hF := length_flatMap_const (List.finRange M.k) _ hlen
  rw [List.length_finRange] at hF
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := decode_layout M _ _ _ _ _
    (if t = 0 then false else tableauAccepted M x (t - 1)) hpre hF
  have hchunk : ∀ τ : Fin M.k,
      ((((idealSources M x t).drop (snapWidth M + 3)).drop (τ * (snapWidth M + 1))).take
        (snapWidth M + 1)) = idealTapeBits M x t τ := by
    intro τ
    rw [idealSources, h5, take_drop_flatMap_append _ _ hlen _ (by simp)]
    simp
  have hin := snapshotAt_inputSymbol hM x t
  unfold tableauStep
  simp only [idealSources] at h1 h2 h3 h4 h6 hchunk ⊢
  simp only [h1, h2, h3, h4, h6, hchunk, option_isSome_getD]
  cases t with
  | zero =>
    simp only [decide_true, if_true]
    have h0 := snapshotAt_zero M x
    have hacc : tableauAccepted M x 0 = false := by simp [tableauAccepted]
    rw [hacc]
    congr 2
    refine Prod.ext (by rw [h0]) (Prod.ext ?_ (by rw [h0]))
    exact hin.symm
  | succ t =>
    simp only [Nat.add_one_ne_zero, decide_false, if_false, Bool.false_eq_true,
      Nat.add_sub_cancel, snapDecode_snapEncode]
    congr 2
    · refine Prod.ext (snapshotAt_state_succ M x t).symm (Prod.ext hin.symm ?_)
      funext τ
      rw [snapshotAt_workSymbol hM x (t + 1) τ]
      unfold idealTapeBits
      cases hp : prevVisit M x.length (t + 1) τ <;> simp [hp, List.replicate_succ]
    · rw [Bool.eq_iff_iff]
      simp only [tableauAccepted, Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro (⟨s, hs, he⟩ | he)
        · exact ⟨s, by omega, he⟩
        · exact ⟨t, by omega, he⟩
      · rintro ⟨s, hs, he⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
        · exact Or.inl ⟨s, hs, he⟩
        · exact Or.inr he

/-- **The sources carry the ideal bits.**  If the vertex values `vals` hold the input `x`
(of length `n`), the two constants, and — for every step `s < t` — the encoding of
snapshot `s` and the accumulator after step `s`, then the sources of step `t` carry
exactly `Complexity.idealSources M x t`.

**Proof sketch.** Map the vertex values over the four parts of the source list.  The
previous block gives the previous snapshot's encoding by hypothesis (constants `0` at
step `0`).  The time-`0` flag and input-presence flag are constants.  The input vertex
`p − 1` holds `x[p − 1]` when `1 ≤ p ≤ n`, and otherwise the input symbol is blank
(position `0` or past the end).  Each work tape's sources give `1` and the last-visit
snapshot's encoding (the visit is strictly earlier, `Complexity.prevVisit_lt`), or
constants on a first visit.  The accumulator comes from the previous segment. -/
theorem tableauSources_map_getD {n : ℕ} (x : List Bool) (hn : x.length = n) (t : ℕ)
    (vals : List Bool) (hin : ∀ (i : ℕ) (h : i < x.length), vals.getD i false = x[i])
    (hF : vals.getD n false = false) (hT : vals.getD (n + 1) false = true)
    (hblk : ∀ s < t,
      (tableauBlock M n s).map (fun v => vals.getD v false) = snapEncode M (snapshotAt M x s) ∧
      vals.getD (tableauVertex M n s (snapWidth M)) false = tableauAccepted M x s) :
    (tableauSources M n t).map (fun v => vals.getD v false) = idealSources M x t := by
  subst hn
  have hconst : ∀ b, vals.getD (tableauConst x.length b) false = b := by
    intro b
    cases b
    · simpa only [tableauConst, Bool.false_eq_true, if_false] using hF
    · simpa only [tableauConst, if_true] using hT
  -- the input symbol at the scheduled position
  set p := inputPosAt M x.length t with hp
  have hinput : decide (1 ≤ p ∧ p ≤ x.length) = (inputBitAt x p).isSome ∧
      vals.getD (if 1 ≤ p ∧ p ≤ x.length then p - 1 else tableauConst x.length false) false =
        (inputBitAt x p).getD false := by
    by_cases h : 1 ≤ p ∧ p ≤ x.length
    · have hx : inputBitAt x p = some x[p - 1] := by
        simp [inputBitAt, show p ≠ 0 by omega, List.getElem?_eq_getElem (show p - 1 < x.length
          by omega)]
      rw [if_pos h, hx, hin (p - 1) (by omega)]
      simp [h]
    · have hx : inputBitAt x p = none := by
        unfold inputBitAt
        split_ifs with h0
        · rfl
        · exact List.getElem?_eq_none (by omega)
      rw [if_neg h, hx, hconst]
      simp [h]
  -- the previous block
  have hpre : (if t = 0 then List.replicate (snapWidth M) (tableauConst x.length false)
      else tableauBlock M x.length (t - 1)).map (fun v => vals.getD v false) =
      if t = 0 then List.replicate (snapWidth M) false
        else snapEncode M (snapshotAt M x (t - 1)) := by
    split_ifs with h
    · simp only [List.map_replicate, hconst]
    · exact (hblk (t - 1) (by omega)).1
  -- the last-visit blocks
  have htape : ∀ τ, (tableauTapeSources M x.length t τ).map (fun v => vals.getD v false) =
      idealTapeBits M x t τ := by
    intro τ
    unfold tableauTapeSources idealTapeBits
    cases hv : prevVisit M x.length t τ with
    | none => simp only [List.map_replicate, hconst]
    | some s => simp only [List.map_cons, hconst, (hblk s (prevVisit_lt M hv)).1]
  -- the previous accumulator
  have hacc : vals.getD (if t = 0 then tableauConst x.length false
      else tableauVertex M x.length (t - 1) (snapWidth M)) false =
      if t = 0 then false else tableauAccepted M x (t - 1) := by
    split_ifs with h
    · exact hconst false
    · exact (hblk (t - 1) (by omega)).2
  simp only [tableauSources, idealSources, List.map_append, List.map_cons, List.map_nil,
    List.map_flatMap, hpre, hconst, ← hp, hinput.1, hinput.2, htape, hacc]

/-- **The tableau invariant.**  After the first `t` segments, the vertex values hold the
input, the two constants, and for every `s < t` the encoding of snapshot `s` and the
accumulator after step `s`.

**Proof sketch.** Induction on `t`.  The constant gates give the base case.  Adding
segment `t` preserves all earlier vertices; its sources carry the ideal bits
(`Complexity.tableauSources_map_getD`), so its gadgets output `tableauStep` of the ideal
bits, which is the encoding of snapshot `t` and the accumulator
(`Complexity.tableauStep_idealSources`). -/
theorem tableauGates_values {M : FinTM Bool} (hM : M.Oblivious) {n : ℕ} (x : List Bool)
    (hn : x.length = n) (t : ℕ) :
    (∀ (i : ℕ) (h : i < x.length),
      (runWith DAGGate.eval (tableauGates M n t) x).getD i false = x[i]) ∧
    (runWith DAGGate.eval (tableauGates M n t) x).getD n false = false ∧
    (runWith DAGGate.eval (tableauGates M n t) x).getD (n + 1) false = true ∧
    ∀ s < t,
      (tableauBlock M n s).map
          (fun v => (runWith DAGGate.eval (tableauGates M n t) x).getD v false) =
        snapEncode M (snapshotAt M x s) ∧
      (runWith DAGGate.eval (tableauGates M n t) x).getD (tableauVertex M n s (snapWidth M))
        false = tableauAccepted M x s := by
  induction t with
  | zero =>
    have h0 : runWith DAGGate.eval (tableauGates M n 0) x = x ++ [false, true] := by
      have := runWith_eval_constGates [false, true] x
      simpa [tableauGates] using this
    rw [h0]
    refine ⟨fun i h => ?_, ?_, ?_, fun s hs => absurd hs (Nat.not_lt_zero _)⟩
    · rw [List.getD_append _ _ _ _ h, List.getD_eq_getElem _ _ h]
    · subst hn; simp
    · subst hn; simp
  | succ t ih =>
    obtain ⟨hin, hF, hT, hblk⟩ := ih
    set V := runWith DAGGate.eval (tableauGates M n t) x with hV
    have hlenV : V.length = tableauBase M n t := by
      rw [hV, length_runWith, length_tableauGates, tableauBase, hn]; omega
    have hstep : runWith DAGGate.eval (tableauGates M n (t + 1)) x =
        runWith DAGGate.eval (embedAll (tableauGadgets M) (tableauSources M n t)
          V.length) V := by
      rw [tableauGates, runWith_append, ← hV, hlenV]
    have hold : ∀ v < tableauBase M n t,
        (runWith DAGGate.eval (tableauGates M n (t + 1)) x).getD v false = V.getD v false := by
      intro v hv
      rw [hstep]
      exact runWith_getD_of_lt _ _ _ (by omega) _
    have hsrc := tableauSources_map_getD M x hn t V hin hF hT hblk
    have hnew : ∀ j ≤ snapWidth M,
        (runWith DAGGate.eval (tableauGates M n (t + 1)) x).getD (tableauVertex M n t j) false =
          (snapEncode M (snapshotAt M x t) ++ [tableauAccepted M x t]).getD j false := by
      intro j hj
      rw [hstep, tableauVertex, ← hlenV,
        runWith_embedAll_getD _ _ (length_tableauSources M n t) V
          (fun a ha => hlenV ▸ tableauSources_lt M n t a ha) (by simp; omega)]
      simp only [tableauGadgets, List.getElem_map, List.getElem_range, gadget_eval]
      rw [ofFn_getD_eq_map _ (length_tableauSources M n t) (fun v => V.getD v false), hsrc,
        tableauStep_idealSources hM]
    have hbase : ∀ s < t, ∀ j ≤ snapWidth M, tableauVertex M n s j < tableauBase M n t :=
      fun s hs j hj => (tableauVertex_lt M n s hj).trans_le (tableauBase_mono M n hs)
    refine ⟨fun i h => ?_, ?_, ?_, fun s hs => ?_⟩
    · rw [hold i (by have := tableauConst_lt M n t false; simp [tableauConst] at this; omega)]
      exact hin i h
    · rw [hold n (by have := tableauConst_lt M n t false; simpa [tableauConst] using this)]
      exact hF
    · rw [hold (n + 1) (by have := tableauConst_lt M n t true; simpa [tableauConst] using this)]
      exact hT
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
      · rw [hold _ (hbase s hs _ (le_refl _))]
        refine ⟨?_, (hblk s hs).2⟩
        rw [← (hblk s hs).1]
        apply List.map_congr_left
        intro v hv
        simp only [tableauBlock, List.mem_map, List.mem_range] at hv
        obtain ⟨j, hj, rfl⟩ := hv
        exact hold _ (hbase s hs j hj.le)
      · refine ⟨?_, ?_⟩
        · apply List.ext_getElem (by simp)
          intro i h1 h2
          simp only [tableauBlock, List.getElem_map, List.getElem_range]
          rw [hnew i (by simp at h1; omega), List.getD_append _ _ _ _ (by simpa using h2),
            List.getD_eq_getElem _ _ h2]
        · rw [hnew _ (le_refl _), List.getD_append_right _ _ _ _ (by simp)]
          simp

/-- **Correctness of the tableau circuit** [AB09, Thm 6.6, proof]: for an oblivious
machine, the circuit outputs `1` on `x` iff some step `s < T` of the run on `x` emits the
bit `1`.

**Proof sketch.** By induction on `t`, after the first `t + 1` segments the block of
segment `s ≤ t` holds the encoding of snapshot `s` and its accumulator holds
"some step `< s` emitted `1`".  For the inductive step, the sources of segment `t` carry
(by the induction hypothesis, the input vertices and the constants) exactly the
*ideal* source bits: the encoding of snapshot `t − 1`, the input symbol at the
scheduled position, and the encodings of the last-visit snapshots.  The gadgets compute
`tableauStep` on them, which is the encoding of snapshot `t` by the three locality
theorems of `CookLevin/Snapshot.lean`. -/
theorem tableauCircuit_eval {M : FinTM Bool} (hM : M.Oblivious) (n T : ℕ) (x : Fin n → Bool) :
    (tableauCircuit M n T).eval x =
      decide (∃ s < T, emitted M (snapshotAt M (List.ofFn x) s) = some true) := by
  have h := (tableauGates_values hM (List.ofFn x) (List.length_ofFn) (T + 1)).2.2.2 T
    (Nat.lt_succ_self T)
  exact h.2

/-- If `M` halts on `x` within `t` steps with output exactly `[b]`, then "some step
before `t` emits `1`" is `b`: the output tape is the concatenation of the emissions. -/
theorem decide_emits_eq_of_computesInTime {M : FinTM Bool} {x : List Bool} {b : Bool}
    {t : ℕ} (h : M.ComputesInTime x [b] t) :
    decide (∃ s < t, emitted M (snapshotAt M x s) = some true) = b := by
  obtain ⟨-, ho⟩ := (FinTM.computesInTime_iff _ _ _ _).mp h
  rw [output_runFrom_eq_flatMap] at ho
  have key : (∃ s < t, emitted M (snapshotAt M x s) = some true) ↔ true ∈ [b] := by
    rw [← ho]
    simp [List.mem_flatMap, Option.mem_toList]
  rw [Bool.eq_iff_iff, decide_eq_true_iff, key]
  simp [eq_comm]

/-- For a machine deciding `L` within `T`, "some step before the deadline emits `1`" is
exactly membership in `L`: the output tape at the deadline is the answer bit alone. -/
theorem decide_emits_eq_indicator {M : FinTM Bool} {L : Language Bool} {T : ℕ → ℕ}
    (hD : M.DecidesInTime L T) (x : List Bool) :
    decide (∃ s < T x.length, emitted M (snapshotAt M x s) = some true) =
      MultiTapeTM.indicator (L : Set (List Bool)) x :=
  decide_emits_eq_of_computesInTime (hD x)

/-- If the oblivious machine `M` decides `L` within `T`, the tableau circuit for length `n`
and budget `T n` decides `L` on inputs of length `n`.  [AB09, Thm 6.6, proof] -/
theorem tableauCircuit_eval_of_decidesInTime {M : FinTM Bool} (hM : M.Oblivious)
    {L : Language Bool} {T : ℕ → ℕ} (hD : M.DecidesInTime L T) (n : ℕ) (x : Fin n → Bool) :
    (tableauCircuit M n (T n)).eval x =
      MultiTapeTM.indicator (L : Set (List Bool)) (List.ofFn x) := by
  rw [tableauCircuit_eval hM]
  have := decide_emits_eq_indicator hD (List.ofFn x)
  rwa [List.length_ofFn] at this

/-- **The tableau theorem** ([AB09, Thm 6.6], the circuit construction of its proof, for a
general time bound): if an oblivious machine `M` decides `L` within `T`, then for every
`n` there is a fan-in-two circuit on `n` inputs of size at most `K_M · (T n + n + 1)`
deciding `L` on length-`n` inputs, with `K_M` depending only on `M`.  The circuit is
`Complexity.tableauCircuit M n (T n)` (see the module docstring for its explicit
structure).

The book states `O(T(n))`; the extra `n + 1` is because the model counts the `n` input
vertices in the size (and needs one vertex even when `T n = 0`). -/
theorem exists_tableau_circuit {M : FinTM Bool} (hM : M.Oblivious) {L : Language Bool}
    {T : ℕ → ℕ} (hD : M.DecidesInTime L T) :
    ∃ K : ℕ, ∀ n, ∃ C : DAGCircuit n, C.IsFaninTwo ∧ C.size ≤ K * (T n + n + 1) ∧
      ∀ x : Fin n → Bool, C.eval x = MultiTapeTM.indicator (L : Set (List Bool)) (List.ofFn x) :=
  ⟨tableauWidth M + 2, fun n => ⟨tableauCircuit M n (T n), tableauCircuit_isFaninTwo M n (T n),
    by rw [tableauCircuit_size]; nlinarith, tableauCircuit_eval_of_decidesInTime hM hD n⟩⟩

end Complexity
