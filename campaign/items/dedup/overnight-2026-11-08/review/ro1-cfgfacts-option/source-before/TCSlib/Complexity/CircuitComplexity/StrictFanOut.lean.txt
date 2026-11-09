/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.StrictSize

/-!
# Fan-out two in the literal circuit model

[AB09, p. 108]: "fan-out 2 can be used to trivially implement arbitrary fan-out."
`FanOut.lean` proves this in the library's relaxed model, using fan-in-one `∧` gates as
copies.  Here the copies are `¬¬v` (two `¬` gates), which the literal model of
[AB09, Def 6.1] allows, and we combine the reduction with strictification
(`StrictCircuit.lean`, `StrictSize.lean`).

## Main definitions

* `BoolCircuit.nnStep`, `BoolCircuit.nnGates`, `BoolCircuit.NNInv` — the `¬¬` reduction and
  its invariant.
* `BoolCircuit.DAGCircuit.fanoutTwoNN` — the `¬¬` fan-out-two version of a circuit whose
  gates are strict.

## Main results

* `BoolCircuit.DAGCircuit.exists_fanoutTwo_notNot` — a circuit with strict gates of size
  `S` has an equivalent one with strict gates and fan-out at most two of size at most `5S`
  (the `¬¬` variant of [AB09, p. 108]).
* `BoolCircuit.DAGCircuit.IsStrict.exists_fanoutTwo` — a strict circuit of size `S` has an
  equivalent strict circuit of fan-out at most two of size at most `20S`.
* `BoolCircuit.DAGCircuit.exists_isStrict_fanoutTwo` — for `n ≥ 1`, a fan-in-two circuit of
  size `S` has an equivalent strict circuit of fan-out at most two of size at most
  `20S + 60`.

## Divergences from [AB09, p. 108]

* **Explicit constants.**  The book gives no bound ("trivially").  The `¬¬` reduction alone
  costs `5S`.  It leaves the final copy of each vertex unread, i.e. extra sinks; making
  the circuit literal again (`DAGCircuit.seal`) costs another factor `4`.

## Implementation note

`nnStep` / `NNInv` / `nnInv_step` parallel `foStep` / `FoInv` / `foInv_step` of
`FanOut.lean`, with a two-gate buffer `¬¬` in place of the one-gate buffer `∧(·)`.  We did
not share code, for two reasons.  First, parameterizing `FanOut.lean` by the buffer gadget
would rewrite an accepted file's proofs: the buffer's length, its internal read (the first
`¬` is read once by the second) and its value argument all enter the invariant.  Second,
deriving the variant from `exists_fanoutTwo` by replacing each `∧(·)` buffer with `¬¬`
needs a variable-length vertex renaming (one or two gates per gate) with its own
value/fan-out invariant, which is no shorter.  The two invariants differ only in the
`gates_ok` predicate (strict versus fan-in two) and the length factor (`5` versus `3`).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, Definition 6.1 and p. 108.)
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

variable {n : ℕ}

/-! ## Helpers -/

/-- A `¬` gate at gate index `i` reading `w` makes vertex `n + i` the negation of `w`. -/
private theorem vertexValue_not_gate {gs : List DAGGate} {i w : ℕ} (hi : i < gs.length)
    (hg : gs[i] = ⟨.not, [w]⟩) (hw : w < n + i) (x : Fin n → Bool) :
    vertexValue gs x (n + i) = !vertexValue gs x w := by
  have key := runWith_getD_gate DAGGate.eval gs (List.ofFn x) hi false
  rw [List.length_ofFn, hg] at key
  simp only [DAGGate.eval, List.all_cons, List.all_nil, Bool.and_true] at key
  rw [runWith_getD_take _ _ _ hi.le (by simpa using hw)] at key
  exact key

/-- Exactly one `j < k` has `c + j = u` when `c ≤ u < c + k`, and none otherwise. -/
private theorem countP_range_add (c u k : ℕ) :
    (List.range k).countP (fun j => decide (u = c + j)) = if c ≤ u ∧ u < c + k then 1 else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.countP_append, ih]
    simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq]
    split_ifs <;> omega

/-- Indexing into the second part of a concatenation. -/
private theorem getElem_append_of_eq {α : Type} {l₁ l₂ : List α} {i j : ℕ}
    (h : i = l₁.length + j) (hj : j < l₂.length) (hi : i < (l₁ ++ l₂).length) :
    (l₁ ++ l₂)[i] = l₂[j] := by
  subst h; simp [List.getElem_append_right]

/-! ## The `¬¬` fan-out reduction -/

/-- One step of the `¬¬` fan-out reduction, for the old gate `g` at old vertex `N`; the
state is the new gates `gs` and the current *tap* of every old vertex.  Append the copy
`g'` of `g` reading the taps of its inputs (vertex `base = n + |gs|`), then for each input
`a` (the `j`-th) the gate `¬(tap a)` (vertex `base + 1 + j`), then for each input the gate
`¬¬(tap a)` (vertex `base + 1 + k + j`, `k` the fan-in), which becomes `a`'s new tap; `g'`
becomes the tap of `N`. -/
def nnStep (n : ℕ) (s : List DAGGate × (ℕ → ℕ) × ℕ) (g : DAGGate) :
    List DAGGate × (ℕ → ℕ) × ℕ :=
  let gs := s.1
  let tap := s.2.1
  let N := s.2.2
  let base := n + gs.length
  let k := g.args.length
  (gs ++ ((⟨g.kind, g.args.map tap⟩ :: g.args.map fun a => ⟨.not, [tap a]⟩) ++
      (List.range k).map fun j => ⟨.not, [base + 1 + j]⟩),
    fun v => if v = N then base else if v ∈ g.args then base + 1 + k + g.args.idxOf v
      else tap v,
    N + 1)

/-- Run the `¬¬` fan-out reduction over a gate list, the inputs being their own taps. -/
def nnGates (n : ℕ) (old : List DAGGate) : List DAGGate × (ℕ → ℕ) × ℕ :=
  old.foldl (nnStep n) ([], id, n)

/-- The invariant of the `¬¬` reduction after the old gates `old`: the taps are distinct,
unread, and carry the old values; every vertex is read at most twice; every new gate is
strict; at most five new gates per old gate. -/
structure NNInv (n : ℕ) (old : List DAGGate) (s : List DAGGate × (ℕ → ℕ) × ℕ) : Prop where
  count : s.2.2 = n + old.length
  acyclic : GatesAcyclic n s.1
  tap_lt : ∀ v < n + old.length, s.2.1 v < n + s.1.length
  tap_inj : ∀ v < n + old.length, ∀ w < n + old.length, s.2.1 v = s.2.1 w → v = w
  value : ∀ x : Fin n → Bool, ∀ v < n + old.length,
    vertexValue s.1 x (s.2.1 v) = (runWith DAGGate.eval old (List.ofFn x)).getD v false
  fanout_le : ∀ u, fanoutIn s.1 u ≤ 2
  fanout_tap : ∀ v < n + old.length, fanoutIn s.1 (s.2.1 v) = 0
  gates_ok : ∀ h ∈ s.1, h.Strict
  length_le : s.1.length ≤ 5 * old.length

/-- The invariant holds initially. -/
theorem nnInv_nil : NNInv n [] ([], id, n) := by
  refine ⟨by simp, GatesAcyclic.nil, fun v hv => by simpa using hv, fun v _ w _ h => h,
    fun x v hv => rfl, fun u => by simp [fanoutIn], fun v _ => by simp [fanoutIn],
    by simp, by simp⟩

/-- One step of the `¬¬` reduction preserves the invariant.

**Proof sketch.** The new gates are the copy `g'` of `g` reading the taps of `g`'s inputs,
the first negations `¬(tap a)`, and the second negations `¬¬(tap a)` reading the first
ones; all read existing vertices.  New taps: `g'` for the new old vertex, the second
negation of `a` for each input `a`, unchanged otherwise; they are distinct (old taps lie
below `g'`, second negations above the first ones, in input order) and unread.  Fan-out: a
tap `tap a` of an input, previously unread, is now read by `g'` and by its first negation,
exactly twice since the inputs are distinct; a first negation is read once, by its second
negation; other vertices keep their fan-out.  Values: `g'` computes `g` on the old values,
and `¬¬(tap a)` has the value of `tap a`.  Strictness transfers to `g'` because taps are
injective, and the length grows by `1 + 2k ≤ 5`. -/
theorem nnInv_step {old : List DAGGate} {g : DAGGate} {s : List DAGGate × (ℕ → ℕ) × ℕ}
    (hinv : NNInv n old s) (hold : GatesAcyclic n (old ++ [g])) (hg : g.Strict) :
    NNInv n (old ++ [g]) (nnStep n s g) := by
  obtain ⟨gs, tap, N⟩ := s
  obtain ⟨hcount, hac, htlt, htinj, hval, hfle, hftap, hok, hlen⟩ := hinv
  dsimp only at hcount hac htlt htinj hval hfle hftap hok hlen
  subst hcount
  set base := n + gs.length with hbase
  set k := g.args.length with hk
  set g' : DAGGate := ⟨g.kind, g.args.map tap⟩ with hg'
  set b1 : List DAGGate := g.args.map fun a => ⟨.not, [tap a]⟩ with hb1
  set b2 : List DAGGate := (List.range k).map fun j => ⟨.not, [base + 1 + j]⟩ with hb2
  set T : ℕ → ℕ := fun v => if v = n + old.length then base
    else if v ∈ g.args then base + 1 + k + g.args.idxOf v else tap v with hT
  have hstep : nnStep n (gs, tap, n + old.length) g =
      (gs ++ ((g' :: b1) ++ b2), T, n + old.length + 1) := rfl
  rw [hstep]
  have hglt : ∀ a ∈ g.args, a < n + old.length := fun a ha => by
    have := hold old.length (by simp) a (by simpa using ha); exact this
  have hta : ∀ a ∈ g.args, tap a < base := fun a ha => htlt a (hglt a ha)
  have hlen_old : n + (old ++ [g]).length = n + old.length + 1 := by simp; omega
  have hk2 : k ≤ 2 := hg.faninTwo.2
  have hl1 : (g' :: b1).length = 1 + k := by simp [hb1, hk]; omega
  have hgslen : (gs ++ ((g' :: b1) ++ b2)).length = gs.length + 1 + 2 * k := by
    simp [hb1, hb2, hk]; omega
  -- reads of the new gates
  have hreadsA : ∀ h ∈ g' :: b1, ∀ a ∈ h.args, ∃ b ∈ g.args, a = tap b := by
    intro h hh a ha
    rcases List.mem_cons.mp hh with rfl | hh
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha; exact ⟨b, hb, rfl⟩
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hh
      simp only [List.mem_singleton] at ha
      exact ⟨b, hb, ha⟩
  have hreadsB : ∀ h ∈ b2, ∀ a ∈ h.args, base < a := by
    intro h hh a ha
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hh
    simp only [List.mem_singleton] at ha
    omega
  -- fan-out added by the new gates
  have hfanA_zero : ∀ u, (∀ b ∈ g.args, tap b ≠ u) → fanoutIn (g' :: b1) u = 0 := by
    intro u hu
    rw [fanoutIn, List.countP_eq_zero]
    intro h hh hmem
    obtain ⟨b, hb, rfl⟩ := hreadsA h hh u (of_decide_eq_true hmem)
    exact hu b hb rfl
  have hfanA_tap : ∀ a ∈ g.args, fanoutIn (g' :: b1) (tap a) = 2 := by
    intro a ha
    have hcnt : fanoutIn b1 (tap a) = 1 := by
      rw [fanoutIn, hb1, List.countP_map]
      have : (g.args.countP ((fun g => decide (tap a ∈ g.args)) ∘
          fun a => (⟨.not, [tap a]⟩ : DAGGate))) = g.args.countP (fun b => b == a) := by
        apply List.countP_congr
        intro b hb
        simp only [Function.comp_apply, List.mem_singleton, decide_eq_true_eq, beq_iff_eq]
        exact ⟨fun h => htinj b (hglt b hb) a (hglt a ha) h.symm, fun h => h ▸ rfl⟩
      rw [this, ← List.count_eq_countP]
      exact List.count_eq_one_of_mem hg.1 ha
    have hhead : (decide (tap a ∈ g'.args)) = true := by
      simp only [hg', decide_eq_true_eq]; exact List.mem_map_of_mem ha
    rw [fanoutIn, List.countP_cons, ← fanoutIn, hcnt, hhead]
    rfl
  have hfanB : ∀ u, fanoutIn b2 u = if base + 1 ≤ u ∧ u < base + 1 + k then 1 else 0 := by
    intro u
    rw [← countP_range_add, fanoutIn, hb2, List.countP_map]
    apply List.countP_congr
    intro j _
    simp
  have hfan_new : ∀ u, fanoutIn (gs ++ ((g' :: b1) ++ b2)) u =
      fanoutIn gs u + fanoutIn (g' :: b1) u + fanoutIn b2 u := by
    intro u; rw [fanoutIn_append, fanoutIn_append]; omega
  have hgs_zero : ∀ u, base ≤ u → fanoutIn gs u = 0 := fun u hu => fanoutIn_eq_zero_of_le hac hu
  refine ⟨by simp only [List.length_append, List.length_singleton]; omega,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- acyclicity
    refine gatesAcyclic_append.mpr ⟨hac, gatesAcyclic_append.mpr ⟨?_, ?_⟩⟩
    · intro i hi a ha
      obtain ⟨b, hb, rfl⟩ := hreadsA _ (List.getElem_mem hi) a ha
      have := hta b hb; omega
    · intro i hi a ha
      simp only [hb2, List.getElem_map, List.getElem_range, List.mem_singleton] at ha
      have : b2.length = k := by simp [hb2]
      have := hl1; subst ha; omega
  · -- tap_lt
    intro v hv
    rw [hlen_old] at hv
    rw [hgslen]
    simp only [hT]
    split_ifs with h1 h2
    · omega
    · have := List.idxOf_lt_length_of_mem h2; omega
    · have := htlt v (by omega); omega
  · -- tap_inj
    intro v hv w hw hvw
    rw [hlen_old] at hv hw
    simp only [hT] at hvw
    split_ifs at hvw with h1 h2 h3 h4 h3 h4 h3 h4
    all_goals first
      | omega
      | (have := htlt v (by omega); omega)
      | (have := htlt w (by omega); omega)
      | (exact (List.idxOf_inj (by assumption) (by assumption)).mp (by omega))
      | exact htinj v (by omega) w (by omega) hvw
  · -- value
    intro x v hv
    dsimp only
    rw [hlen_old] at hv
    have hold_val : ∀ v < n + old.length,
        (runWith DAGGate.eval (old ++ [g]) (List.ofFn x)).getD v false =
          (runWith DAGGate.eval old (List.ofFn x)).getD v false := fun v hv => by
      rw [runWith_append, runWith_getD_of_lt]; simpa using hv
    by_cases h1 : v = n + old.length
    · -- the copy of `g` computes `g` on the taps of its inputs
      subst h1
      have hTv : T (n + old.length) = base := by simp [hT]
      rw [hTv]
      have hlast : (runWith DAGGate.eval (old ++ [g]) (List.ofFn x)).getD (n + old.length)
          false = g.eval (runWith DAGGate.eval old (List.ofFn x)) := by
        have := runWith_getD_last DAGGate.eval old g (List.ofFn x) false
        rwa [List.length_ofFn] at this
      rw [hlast, List.cons_append, List.append_cons, vertexValue_append _ _ _ (by simp [hbase]),
        vertexValue_last]
      exact DAGGate.eval_remap g tap fun a ha => hval x a (hglt a ha)
    by_cases h2 : v ∈ g.args
    · -- the second negation copies the old tap of its input
      have hTv : T v = base + 1 + k + g.args.idxOf v := by simp [hT, h1, h2]
      rw [hTv]
      have hjk : g.args.idxOf v < k := List.idxOf_lt_length_of_mem h2
      have hb2len : b2.length = k := by simp [hb2]
      have hb1len : b1.length = k := by simp [hb1, hk]
      have hi2 : gs.length + 1 + k + g.args.idxOf v < (gs ++ ((g' :: b1) ++ b2)).length := by
        rw [hgslen]; omega
      have hi1 : gs.length + 1 + g.args.idxOf v < (gs ++ ((g' :: b1) ++ b2)).length := by
        rw [hgslen]; omega
      have hget2 : (gs ++ ((g' :: b1) ++ b2))[gs.length + 1 + k + g.args.idxOf v] =
          ⟨.not, [base + 1 + g.args.idxOf v]⟩ := by
        rw [getElem_append_of_eq (j := 1 + k + g.args.idxOf v) (by omega) (by simp; omega),
          getElem_append_of_eq (j := g.args.idxOf v) (by rw [hl1]) (by omega)]
        simp [hb2]
      have hget1 : (gs ++ ((g' :: b1) ++ b2))[gs.length + 1 + g.args.idxOf v] =
          ⟨.not, [tap v]⟩ := by
        rw [getElem_append_of_eq (j := 1 + g.args.idxOf v) (by omega) (by simp; omega),
          List.getElem_append_left (by rw [hl1]; omega)]
        simp [Nat.add_comm 1, hb1]
      have e2 := vertexValue_not_gate hi2 hget2 (by omega) x
      have e1 := vertexValue_not_gate hi1 hget1 (by have := hta v h2; omega) x
      rw [show base + 1 + k + g.args.idxOf v = n + (gs.length + 1 + k + g.args.idxOf v) by omega,
        e2, show base + 1 + g.args.idxOf v = n + (gs.length + 1 + g.args.idxOf v) by omega, e1,
        Bool.not_not, vertexValue_append _ _ _ (hta v h2), hval x v (hglt v h2),
        hold_val v (hglt v h2)]
    · -- an untouched tap
      have hTv : T v = tap v := by simp [hT, h1, h2]
      rw [hTv, vertexValue_append _ _ _ (htlt v (by omega)), hval x v (by omega),
        hold_val v (by omega)]
  · -- fanout_le
    intro u
    rw [hfan_new, hfanB]
    by_cases hu : ∃ b ∈ g.args, tap b = u
    · obtain ⟨b, hb, rfl⟩ := hu
      rw [hftap b (hglt b hb), hfanA_tap b hb]
      have := hta b hb
      split_ifs <;> omega
    · push_neg at hu
      rw [hfanA_zero u hu]
      by_cases hub : base ≤ u
      · rw [hgs_zero u hub]; split_ifs <;> omega
      · have := hfle u; split_ifs <;> omega
  · -- fanout_tap
    intro v hv
    dsimp only
    rw [hlen_old] at hv
    by_cases h1 : v = n + old.length
    · have hTv : T v = base := by simp [hT, h1]
      rw [hTv, hfan_new, hfanB, hgs_zero _ le_rfl,
        hfanA_zero _ fun b hb h => by have := hta b hb; omega]
      split_ifs <;> omega
    by_cases h2 : v ∈ g.args
    · have hTv : T v = base + 1 + k + g.args.idxOf v := by simp [hT, h1, h2]
      rw [hTv, hfan_new, hfanB, hgs_zero _ (by omega),
        hfanA_zero _ fun b hb h => by have := hta b hb; omega]
      split_ifs <;> omega
    · have hTv : T v = tap v := by simp [hT, h1, h2]
      rw [hTv, hfan_new, hfanB, hftap v (by omega),
        hfanA_zero _ fun b hb h => h2 (htinj b (hglt b hb) v (by omega) h ▸ hb)]
      have := htlt v (by omega)
      split_ifs <;> omega
  · -- gates_ok
    intro h hh
    rcases List.mem_append.mp hh with hh | hh
    · exact hok h hh
    rcases List.mem_append.mp hh with hh | hh
    · rcases List.mem_cons.mp hh with rfl | hh
      · refine ⟨hg.1.map_on fun a ha b hb h => htinj a (hglt a ha) b (hglt b hb) h, ?_⟩
        simpa [hg'] using hg.2
      · obtain ⟨b, -, rfl⟩ := List.mem_map.mp hh
        simp [DAGGate.Strict]
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hh
      simp [DAGGate.Strict]
  · -- length_le
    rw [hgslen]
    simp only [List.length_append, List.length_singleton]
    omega

/-- The invariant holds after the whole `¬¬` reduction, by induction on the gate list. -/
theorem nnGates_inv : ∀ (old : List DAGGate), GatesAcyclic n old → (∀ g ∈ old, g.Strict) →
    NNInv n old (nnGates n old) := by
  intro old
  induction old using List.reverseRecOn with
  | nil => intro _ _; exact nnInv_nil
  | append_singleton old g ih =>
    intro hac hok
    have hac' : GatesAcyclic n old := (gatesAcyclic_append.mp hac).1
    have := ih hac' fun g' hg' => hok g' (by simp [hg'])
    rw [nnGates, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact nnInv_step this hac (hok g (by simp))

/-! ## Circuits -/

/-- The `¬¬` fan-out-two version of a circuit whose gates are strict: every gate is copied
reading the current taps of its inputs, and each read tap is replaced by a fresh copy
`¬¬tap`.  [AB09, p. 108] -/
def DAGCircuit.fanoutTwoNN (C : DAGCircuit n) (hC : ∀ g ∈ C.gates, g.Strict) : DAGCircuit n where
  gates := (nnGates n C.gates).1
  output := (nnGates n C.gates).2.1 C.output
  args_lt := (nnGates_inv C.gates C.args_lt hC).acyclic
  output_lt := (nnGates_inv C.gates C.args_lt hC).tap_lt _ C.output_lt

section FanoutTwoNN

variable (C : DAGCircuit n) (hC : ∀ g ∈ C.gates, g.Strict)

/-- The `¬¬` version computes the same function. -/
theorem DAGCircuit.fanoutTwoNN_eval (x : Fin n → Bool) :
    (C.fanoutTwoNN hC).eval x = C.eval x :=
  (nnGates_inv C.gates C.args_lt hC).value x _ C.output_lt

/-- Every gate of the `¬¬` version is strict. -/
theorem DAGCircuit.fanoutTwoNN_strict : ∀ g ∈ (C.fanoutTwoNN hC).gates, g.Strict :=
  (nnGates_inv C.gates C.args_lt hC).gates_ok

/-- Every vertex of the `¬¬` version has fan-out at most two. -/
theorem DAGCircuit.fanoutTwoNN_hasFanoutTwo : (C.fanoutTwoNN hC).HasFanoutTwo :=
  (nnGates_inv C.gates C.args_lt hC).fanout_le

/-- The output of the `¬¬` version is not read by any gate. -/
theorem DAGCircuit.fanoutTwoNN_fanout_output :
    (C.fanoutTwoNN hC).fanout (C.fanoutTwoNN hC).output = 0 :=
  (nnGates_inv C.gates C.args_lt hC).fanout_tap _ C.output_lt

/-- Each old gate becomes itself plus two negations per input: at most `5` gates. -/
theorem DAGCircuit.fanoutTwoNN_size_le : (C.fanoutTwoNN hC).size ≤ n + 5 * C.gates.length := by
  have := (nnGates_inv C.gates C.args_lt hC).length_le
  change n + (nnGates n C.gates).1.length ≤ _
  omega

end FanoutTwoNN

/-- **Fan-out two with `¬¬` buffers.**  Every circuit of size `S` whose gates are those of
the literal model of [AB09, Def 6.1] (`∧`/`∨` of fan-in exactly two, `¬` of fan-in one) is
equivalent to a circuit of size at most `5S` with the same kind of gates in which every
vertex has fan-out at most two.  [AB09, p. 108]

This is the variant of `DAGCircuit.exists_fanoutTwo` (`FanOut.lean`, `3S`, fan-in-one `∧`
copies) for the literal model, where a copy is `¬¬v`.  The final copy of each vertex is
left unread (an extra sink); `IsStrict.exists_fanoutTwo` removes those.

**Proof sketch.** As for `exists_fanoutTwo`: process the gates in order, keeping for every
old vertex an unread *tap* holding its value.  An old gate is copied reading the taps of its
(distinct) inputs; then for each input `a` the gates `¬(tap a)` and `¬¬(tap a)` are
added, and the latter becomes `a`'s new tap.  Each tap is read once by a gate copy and once
by a first negation, each first negation once by its second negation, and nothing else
reads them later.  Each old gate costs one copy plus at most four negations. -/
theorem DAGCircuit.exists_fanoutTwo_notNot (C : DAGCircuit n) (hC : ∀ g ∈ C.gates, g.Strict) :
    ∃ C' : DAGCircuit n, (∀ g ∈ C'.gates, g.Strict) ∧ C'.HasFanoutTwo ∧
      (∀ x, C'.eval x = C.eval x) ∧ C'.size ≤ 5 * C.size :=
  ⟨C.fanoutTwoNN hC, C.fanoutTwoNN_strict hC, C.fanoutTwoNN_hasFanoutTwo hC,
    C.fanoutTwoNN_eval hC, (C.fanoutTwoNN_size_le hC).trans (by simp [DAGCircuit.size]; omega)⟩

/-- A circuit of size `S` with strict gates has an equivalent strict circuit of fan-out at
most two and size at most `20S`: the `¬¬` reduction followed by sealing. -/
theorem DAGCircuit.exists_isStrict_fanoutTwo_of_strict (C : DAGCircuit n)
    (hC : ∀ g ∈ C.gates, g.Strict) :
    ∃ C' : DAGCircuit n, C'.IsStrict ∧ C'.HasFanoutTwo ∧ (∀ x, C'.eval x = C.eval x) ∧
      C'.size ≤ 20 * C.size := by
  set D := C.fanoutTwoNN hC
  refine ⟨D.seal, D.seal_isStrict (C.fanoutTwoNN_strict hC),
    D.seal_hasFanoutTwo (C.fanoutTwoNN_hasFanoutTwo hC)
      (by rw [C.fanoutTwoNN_fanout_output hC]; omega),
    fun x => (D.seal_eval x).trans (C.fanoutTwoNN_eval hC x), ?_⟩
  have h1 := D.seal_size_le
  have h2 : D.size ≤ n + 5 * C.gates.length := C.fanoutTwoNN_size_le hC
  simp only [DAGCircuit.size] at h1 h2 ⊢
  omega

/-- **Fan-out two in the literal model.**  Every strict circuit ([AB09, Def 6.1] taken
literally) of size `S` is equivalent to a strict circuit of size at most `20S` in which
every vertex has fan-out at most two.  [AB09, p. 108]

The book gives no bound ("trivially"); the `¬¬` reduction costs `5S` and re-sealing the
unread final copies at most another factor `4`. -/
theorem DAGCircuit.IsStrict.exists_fanoutTwo {C : DAGCircuit n} (hC : C.IsStrict) :
    ∃ C' : DAGCircuit n, C'.IsStrict ∧ C'.HasFanoutTwo ∧ (∀ x, C'.eval x = C.eval x) ∧
      C'.size ≤ 20 * C.size :=
  C.exists_isStrict_fanoutTwo_of_strict hC.1

/-- **Strictification with fan-out two.**  For `n ≥ 1`, every fan-in-two circuit of size
`S` is equivalent to a strict circuit ([AB09, Def 6.1] taken literally) of size at most
`20S + 60` in which every vertex has fan-out at most two.  [AB09, Def 6.1 and p. 108]

**Proof sketch.** `deconst` gives strict gates at size `S + 3`; then the `¬¬` reduction and
sealing (`exists_isStrict_fanoutTwo_of_strict`). -/
theorem DAGCircuit.exists_isStrict_fanoutTwo (C : DAGCircuit n) (hC : C.IsFaninTwo)
    (hn : 0 < n) :
    ∃ C' : DAGCircuit n, C'.IsStrict ∧ C'.HasFanoutTwo ∧ (∀ x, C'.eval x = C.eval x) ∧
      C'.size ≤ 20 * C.size + 60 := by
  obtain ⟨C', h1, h2, h3, h4⟩ :=
    (C.deconst hn).exists_isStrict_fanoutTwo_of_strict (C.deconst_strict hn hC)
  refine ⟨C', h1, h2, fun x => (h3 x).trans (C.deconst_eval hn hC x), ?_⟩
  rw [DAGCircuit.deconst_size] at h4
  omega

end BoolCircuit
