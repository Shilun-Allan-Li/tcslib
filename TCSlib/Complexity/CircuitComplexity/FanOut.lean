/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.DAGFanin

/-!
# Fan-out two suffices

[AB09, p. 108]: "fan-out 2 can be used to trivially implement arbitrary fan-out."  We
define the fan-out of a vertex of a `BoolCircuit.DAGCircuit` ([AB09, Def 6.1]) and show
that every fan-in-two circuit of size `S` is equivalent to a fan-in-two circuit of size at
most `3S` in which every vertex has fan-out at most two.

## Main definitions

* `BoolCircuit.fanoutIn`, `BoolCircuit.DAGCircuit.fanout` — the number of gates reading a
  vertex; `BoolCircuit.DAGCircuit.HasFanoutTwo` — every vertex has fan-out at most two.
* `BoolCircuit.foStep`, `BoolCircuit.foGates`, `BoolCircuit.FoInv` — the reduction and its
  invariant.
* `BoolCircuit.DAGCircuit.fanoutTwo` — the fan-out-two version of a fan-in-two circuit.

## Main results

* `BoolCircuit.DAGCircuit.fanoutTwo_eval`, `fanoutTwo_isFaninTwo`, `fanoutTwo_hasFanoutTwo`,
  `fanoutTwo_size_le` — correctness, fan-in two, fan-out two, size `≤ n + 3 · #gates`.
* `BoolCircuit.DAGCircuit.exists_fanoutTwo` — the headline ([AB09, p. 108]).

## Divergences from [AB09, p. 108]

* **Copies are fan-in-one `∧` gates.**  The model allows an `∧` gate with one input (the
  identity; see `DAGCircuit.lean`), which serves as a buffer.  Under the book's literal
  fan-in-exactly-two convention a buffer would instead be `¬¬v` (two fan-in-one `¬` gates,
  no parallel edges), giving size at most `5S`.  That variant is
  `DAGCircuit.exists_fanoutTwo_notNot` (`StrictFanOut.lean`).  Fully literal circuits
  (`DAGCircuit.IsStrict`) of fan-out two are `DAGCircuit.IsStrict.exists_fanoutTwo` (`20S`)
  and `DAGCircuit.exists_isStrict_fanoutTwo` (`20S + 60` from any fan-in-two circuit,
  `n ≥ 1`).
* **Explicit constant.**  The book gives no size bound ("trivially"); we prove `3S`.
* **Output.**  Fan-out counts gates reading a vertex; designating a vertex as the output is
  not an edge.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, p. 108.)
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

variable {n : ℕ}

/-! ## Fan-out -/

/-- The number of gates of `gs` that read vertex `v`. -/
def fanoutIn (gs : List DAGGate) (v : ℕ) : ℕ :=
  gs.countP fun g => decide (v ∈ g.args)

/-- The fan-out of vertex `v` of a circuit: the number of gates reading it, i.e. its number
of outgoing edges ([AB09, p. 108]).  Being the output does not count as an edge. -/
def DAGCircuit.fanout (C : DAGCircuit n) (v : ℕ) : ℕ := fanoutIn C.gates v

/-- Every vertex of the circuit has fan-out at most two.  [AB09, p. 108] -/
def DAGCircuit.HasFanoutTwo (C : DAGCircuit n) : Prop := ∀ v, C.fanout v ≤ 2

/-- Fan-out over a concatenation is the sum of the fan-outs. -/
theorem fanoutIn_append (gs ext : List DAGGate) (v : ℕ) :
    fanoutIn (gs ++ ext) v = fanoutIn gs v + fanoutIn ext v := by
  simp [fanoutIn, List.countP_append]

/-- A single gate reads `v` once if `v` is among its inputs, and not at all otherwise. -/
theorem fanoutIn_singleton (g : DAGGate) (v : ℕ) :
    fanoutIn [g] v = if v ∈ g.args then 1 else 0 := by
  by_cases h : v ∈ g.args <;> simp [fanoutIn, h]

/-- No gate reads a vertex that does not exist yet. -/
theorem fanoutIn_eq_zero_of_le {gs : List DAGGate} (hgs : GatesAcyclic n gs) {v : ℕ}
    (hv : n + gs.length ≤ v) : fanoutIn gs v = 0 := by
  rw [fanoutIn, List.countP_eq_zero]
  intro g hg hmem
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  have := hgs i hi v (of_decide_eq_true hmem)
  omega

/-- Gate lists whose every gate reads only vertices below `n + gs.length` extend an
acyclic list acyclically. -/
private theorem gatesAcyclic_append_of_lt {gs : List DAGGate} (hgs : GatesAcyclic n gs)
    {ext : List DAGGate}
    (hext : ∀ h ∈ ext, ∀ a ∈ h.args, a < n + gs.length) : GatesAcyclic n (gs ++ ext) := by
  intro i hi a ha
  rcases Nat.lt_or_ge i gs.length with h | h
  · rw [List.getElem_append_left h] at ha
    exact hgs i h a ha
  · rw [List.getElem_append_right h] at ha
    have := hext _ (List.getElem_mem _) a ha
    omega

/-! ## The fan-out reduction -/

/-- One step of the fan-out reduction, for the old gate `g` at old vertex `N`, the state
being the new gates `gs` and the current *tap* of every old vertex (the new vertex later
readers should use).  Append `g` reading the taps of its inputs, then for each input `a` a
buffer `∧(tap a)` (a fan-in-one `∧` gate, the identity), which becomes `a`'s new tap; the
new gate itself becomes the tap of `N`.  Each tap is read once by a gate and once by the
buffer that replaces it, so every vertex has fan-out at most two. -/
def foStep (n : ℕ) (s : List DAGGate × (ℕ → ℕ) × ℕ) (g : DAGGate) :
    List DAGGate × (ℕ → ℕ) × ℕ :=
  let gs := s.1
  let tap := s.2.1
  let N := s.2.2
  let base := n + gs.length
  (gs ++ (⟨g.kind, g.args.map tap⟩ :: g.args.map fun a => ⟨.and, [tap a]⟩),
    fun v => if v = N then base else if v ∈ g.args then base + 1 + g.args.idxOf v else tap v,
    N + 1)

/-- Run the fan-out reduction over a gate list, starting from the inputs as their own taps. -/
def foGates (n : ℕ) (old : List DAGGate) : List DAGGate × (ℕ → ℕ) × ℕ :=
  old.foldl (foStep n) ([], id, n)

/-- The invariant of the fan-out reduction after the old gates `old`. -/
structure FoInv (n : ℕ) (old : List DAGGate) (s : List DAGGate × (ℕ → ℕ) × ℕ) : Prop where
  count : s.2.2 = n + old.length
  acyclic : GatesAcyclic n s.1
  tap_lt : ∀ v < n + old.length, s.2.1 v < n + s.1.length
  tap_inj : ∀ v < n + old.length, ∀ w < n + old.length, s.2.1 v = s.2.1 w → v = w
  value : ∀ x : Fin n → Bool, ∀ v < n + old.length,
    vertexValue s.1 x (s.2.1 v) = (runWith DAGGate.eval old (List.ofFn x)).getD v false
  fanout_le : ∀ u, fanoutIn s.1 u ≤ 2
  fanout_tap : ∀ v < n + old.length, fanoutIn s.1 (s.2.1 v) = 0
  gates_ok : ∀ h ∈ s.1, h.args.Nodup ∧ (h.kind = .not → h.args.length = 1) ∧
    h.args.length ≤ 2
  length_le : s.1.length ≤ 3 * old.length

/-- The invariant holds initially: the inputs are their own unread taps. -/
theorem foInv_nil : FoInv n [] ([], id, n) := by
  refine ⟨by simp, GatesAcyclic.nil, fun v hv => by simpa using hv, fun v _ w _ h => h,
    fun x v hv => rfl, fun u => by simp [fanoutIn], fun v _ => by simp [fanoutIn],
    by simp, by simp⟩

/-- One step of the fan-out reduction preserves the invariant.

**Proof sketch.** The new gates are the copy `g'` of `g`, reading the taps of `g`'s inputs,
and one buffer `∧(tap a)` per input `a`.  They read only taps, which exist, so acyclicity
is kept.  New taps: `g'` for the new old vertex, the buffer of `a` for each input `a`,
unchanged otherwise; these are distinct (old taps lie below `g'`, buffers above, buffers in
input order) and unread (nothing reads `g'` or a buffer yet, and an untouched tap is read
by none of the new gates, by injectivity).  Fan-out: a vertex read by a new gate is a tap
`tap a`, previously unread, now read by `g'` and by `a`'s buffer — exactly twice, since
`g`'s inputs are distinct; other vertices keep their fan-out.  Values: `g'` computes `g`
on the old values (the taps hold them), and a buffer copies its tap.  Well-formedness
transfers because taps are injective, and the length grows by `1 + fan-in ≤ 3`. -/
theorem foInv_step {old : List DAGGate} {g : DAGGate} {s : List DAGGate × (ℕ → ℕ) × ℕ}
    (hinv : FoInv n old s) (hold : GatesAcyclic n (old ++ [g]))
    (hg : g.args.Nodup ∧ (g.kind = .not → g.args.length = 1) ∧ g.args.length ≤ 2) :
    FoInv n (old ++ [g]) (foStep n s g) := by
  obtain ⟨gs, tap, N⟩ := s
  obtain ⟨hcount, hac, htlt, htinj, hval, hfle, hftap, hok, hlen⟩ := hinv
  dsimp only at hcount hac htlt htinj hval hfle hftap hok hlen
  subst hcount
  set base := n + gs.length with hbase
  set g' : DAGGate := ⟨g.kind, g.args.map tap⟩ with hg'
  set bufs : List DAGGate := g.args.map fun a => ⟨.and, [tap a]⟩ with hbufs
  set T : ℕ → ℕ := fun v => if v = n + old.length then base
    else if v ∈ g.args then base + 1 + g.args.idxOf v else tap v with hT
  have hstep : foStep n (gs, tap, n + old.length) g = (gs ++ (g' :: bufs), T,
      n + old.length + 1) := rfl
  rw [hstep]
  have hglt : ∀ a ∈ g.args, a < n + old.length := fun a ha => by
    have := hold old.length (by simp) a (by simpa using ha); exact this
  have hta : ∀ a ∈ g.args, tap a < base := fun a ha => htlt a (hglt a ha)
  have hlen_old : n + (old ++ [g]).length = n + old.length + 1 := by simp; omega
  have hgslen : (gs ++ g' :: bufs).length = gs.length + 1 + g.args.length := by
    simp [hbufs]; omega
  -- the new gates read only taps of `g`'s inputs
  have hnew_reads : ∀ h ∈ g' :: bufs, ∀ a ∈ h.args, ∃ b ∈ g.args, a = tap b := by
    intro h hh a ha
    rcases List.mem_cons.mp hh with rfl | hh
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha; exact ⟨b, hb, rfl⟩
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hh
      simp only [List.mem_singleton] at ha
      exact ⟨b, hb, ha⟩
  -- fan-out added by the new gates
  have hfan_new_zero : ∀ u, (∀ b ∈ g.args, tap b ≠ u) → fanoutIn (g' :: bufs) u = 0 := by
    intro u hu
    rw [fanoutIn, List.countP_eq_zero]
    intro h hh hmem
    obtain ⟨b, hb, rfl⟩ := hnew_reads h hh u (of_decide_eq_true hmem)
    exact hu b hb rfl
  have hfan_new_tap : ∀ a ∈ g.args, fanoutIn (g' :: bufs) (tap a) = 2 := by
    intro a ha
    have hcnt : fanoutIn bufs (tap a) = 1 := by
      rw [fanoutIn, hbufs, List.countP_map]
      have : (g.args.countP ((fun g => decide (tap a ∈ g.args)) ∘
          fun a => (⟨.and, [tap a]⟩ : DAGGate))) = g.args.countP (fun b => b == a) := by
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
  refine ⟨by simp only [List.length_append, List.length_singleton]; omega,
    gatesAcyclic_append_of_lt hac fun h hh a ha => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨b, hb, rfl⟩ := hnew_reads h hh a ha
    exact hta b hb
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
    rw [hlen_old] at hv
    have hold_val : ∀ v < n + old.length,
        (runWith DAGGate.eval (old ++ [g]) (List.ofFn x)).getD v false =
          (runWith DAGGate.eval old (List.ofFn x)).getD v false := fun v hv => by
      rw [runWith_append, runWith_getD_of_lt]; simpa using hv
    simp only [hT]
    split_ifs with h1 h2
    · -- the copy of `g` computes `g` on the taps of its inputs
      subst h1
      have hlast : (runWith DAGGate.eval (old ++ [g]) (List.ofFn x)).getD (n + old.length)
          false = g.eval (runWith DAGGate.eval old (List.ofFn x)) := by
        have := runWith_getD_last DAGGate.eval old g (List.ofFn x) false
        rwa [List.length_ofFn] at this
      rw [hlast, List.append_cons, vertexValue_append _ _ _ (by simp [hbase]),
        vertexValue_last]
      exact DAGGate.eval_remap g tap fun a ha => hval x a (hglt a ha)
    · -- a buffer copies the old tap of its input
      have hj := List.idxOf_lt_length_of_mem h2
      have hi : gs.length + 1 + g.args.idxOf v < (gs ++ g' :: bufs).length := by
        rw [hgslen]; omega
      have key := runWith_getD_gate DAGGate.eval (gs ++ g' :: bufs) (List.ofFn x) hi false
      have hidx : (List.ofFn x).length + (gs.length + 1 + g.args.idxOf v) =
          base + 1 + g.args.idxOf v := by simp [hbase]; omega
      have hget : (gs ++ g' :: bufs)[gs.length + 1 + g.args.idxOf v] =
          (⟨.and, [tap v]⟩ : DAGGate) := by
        rw [List.getElem_append_right (by omega)]
        have : gs.length + 1 + g.args.idxOf v - gs.length = g.args.idxOf v + 1 := by omega
        simp only [this, List.getElem_cons_succ, hbufs, List.getElem_map, List.getElem_idxOf]
      rw [hidx, hget, DAGGate.eval_singleton (by decide),
        runWith_getD_take _ _ _ hi.le (by
          have := hta v h2; simp [hbase] at this ⊢; omega)] at key
      rw [vertexValue, key, ← vertexValue, vertexValue_append _ _ _ (hta v h2),
        hval x v (hglt v h2), hold_val v (hglt v h2)]
    · -- an untouched tap
      rw [vertexValue_append _ _ _ (htlt v (by omega)), hval x v (by omega),
        hold_val v (by omega)]
  · -- fanout_le
    intro u
    rw [fanoutIn_append]
    by_cases hu : ∃ b ∈ g.args, tap b = u
    · obtain ⟨b, hb, rfl⟩ := hu
      rw [hftap b (hglt b hb), hfan_new_tap b hb]
    · push_neg at hu
      rw [hfan_new_zero u hu]
      simpa using hfle u
  · -- fanout_tap
    intro v hv
    rw [hlen_old] at hv
    rw [fanoutIn_append]
    have hge : ∀ u, base ≤ u → fanoutIn gs u + fanoutIn (g' :: bufs) u = 0 := by
      intro u hu
      rw [fanoutIn_eq_zero_of_le hac hu, hfan_new_zero u fun b hb h => by
        have := hta b hb; omega]
    simp only [hT]
    split_ifs with h1 h2
    · exact hge _ le_rfl
    · exact hge _ (by omega)
    · rw [hftap v (by omega), hfan_new_zero (tap v) fun b hb h => by
        have := htinj b (hglt b hb) v (by omega) h
        exact h2 (this ▸ hb)]
  · -- gates_ok
    intro h hh
    rcases List.mem_append.mp hh with hh | hh
    · exact hok h hh
    rcases List.mem_cons.mp hh with rfl | hh
    · refine ⟨hg.1.map_on fun a ha b hb h => htinj a (hglt a ha) b (hglt b hb) h,
        fun hk => by simpa [hg'] using hg.2.1 hk, by simpa [hg'] using hg.2.2⟩
    · obtain ⟨b, -, rfl⟩ := List.mem_map.mp hh
      refine ⟨List.nodup_singleton _, ?_, by simp⟩
      intro h; simp at h
  · -- length_le
    rw [hgslen]
    have := hg.2.2
    simp only [List.length_append, List.length_singleton]
    omega

/-- The invariant holds after the whole reduction, by induction on the gate list. -/
theorem foGates_inv : ∀ (old : List DAGGate), GatesAcyclic n old →
    (∀ g ∈ old, g.args.Nodup ∧ (g.kind = .not → g.args.length = 1) ∧ g.args.length ≤ 2) →
    FoInv n old (foGates n old) := by
  intro old
  induction old using List.reverseRecOn with
  | nil => intro _ _; exact foInv_nil
  | append_singleton old g ih =>
    intro hac hok
    have hac' : GatesAcyclic n old := fun i hi a ha => by
      have := hac i (by simp; omega) a (by rwa [List.getElem_append_left hi])
      exact this
    have := ih hac' fun g' hg' => hok g' (by simp [hg'])
    rw [foGates, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact foInv_step this hac (hok g (by simp))

/-! ## Circuits of fan-out two -/

private theorem gates_ok_of_isFaninTwo {C : DAGCircuit n} (hC : C.IsFaninTwo) :
    ∀ g ∈ C.gates, g.args.Nodup ∧ (g.kind = .not → g.args.length = 1) ∧ g.args.length ≤ 2 :=
  fun g hg => ⟨(hC.1 g hg).1, (hC.1 g hg).2, hC.2 g hg⟩

/-- The fan-out-two version of a fan-in-two circuit: every gate is copied reading the
current taps of its inputs, and each read tap is replaced by a fresh identity buffer
(a fan-in-one `∧` gate).  [AB09, p. 108] -/
def DAGCircuit.fanoutTwo (C : DAGCircuit n) (hC : C.IsFaninTwo) : DAGCircuit n where
  gates := (foGates n C.gates).1
  output := (foGates n C.gates).2.1 C.output
  args_lt := (foGates_inv C.gates C.args_lt (gates_ok_of_isFaninTwo hC)).acyclic
  output_lt := (foGates_inv C.gates C.args_lt (gates_ok_of_isFaninTwo hC)).tap_lt _
    C.output_lt

section FanoutTwo

variable (C : DAGCircuit n) (hC : C.IsFaninTwo)

/-- The fan-out-two version computes the same function. -/
theorem DAGCircuit.fanoutTwo_eval (x : Fin n → Bool) : (C.fanoutTwo hC).eval x = C.eval x :=
  (foGates_inv C.gates C.args_lt (gates_ok_of_isFaninTwo hC)).value x _ C.output_lt

/-- The fan-out-two version has fan-in two. -/
theorem DAGCircuit.fanoutTwo_isFaninTwo : (C.fanoutTwo hC).IsFaninTwo := by
  have h := (foGates_inv C.gates C.args_lt (gates_ok_of_isFaninTwo hC)).gates_ok
  exact ⟨fun g hg => ⟨(h g hg).1, (h g hg).2.1⟩, fun g hg => (h g hg).2.2⟩

/-- Every vertex of the fan-out-two version has fan-out at most two. -/
theorem DAGCircuit.fanoutTwo_hasFanoutTwo : (C.fanoutTwo hC).HasFanoutTwo :=
  (foGates_inv C.gates C.args_lt (gates_ok_of_isFaninTwo hC)).fanout_le

/-- Each old gate becomes itself plus one buffer per input: at most `3` gates. -/
theorem DAGCircuit.fanoutTwo_size_le : (C.fanoutTwo hC).size ≤ n + 3 * C.gates.length := by
  have := (foGates_inv C.gates C.args_lt (gates_ok_of_isFaninTwo hC)).length_le
  change n + (foGates n C.gates).1.length ≤ _
  omega

end FanoutTwo

/-- Fan-out two implements arbitrary fan-out: every fan-in-two circuit of size `S` is
equivalent to a fan-in-two circuit of size at most `3S` in which every vertex has fan-out
at most two.  [AB09, p. 108]

The book's remark ("fan-out 2 can be used to trivially implement arbitrary fan-out") is
stated without a size bound; the construction gives `n + 3 · #gates ≤ 3S`.  The copies are
identity gates, i.e. `∧` gates of fan-in one, which the model allows (a fan-in-one gate is
the identity; see `DAGCircuit.lean`).  Under the book's literal fan-in-exactly-two
convention one would use `¬¬v` (two `¬` gates) as the buffer instead, giving size at most
`5S`.  That variant is `DAGCircuit.exists_fanoutTwo_notNot` (`StrictFanOut.lean`), and
`DAGCircuit.IsStrict.exists_fanoutTwo` stays within the fully literal model.

**Proof sketch.** Process the gates in order, keeping for every old vertex a *tap*: the new
vertex holding its value that has not been read yet (initially the input itself).  An old
gate is copied reading the taps of its (distinct) inputs; then for each input a buffer
`∧(tap)` is added, which becomes that input's new tap, and the copy becomes the tap of the
new old vertex.  Invariant: taps are distinct and unread, every vertex is read at most
twice (a tap is read once by a gate copy and once by the buffer replacing it, and never
again), and each tap holds its old vertex's value.  Each old gate costs one copy plus at
most two buffers. -/
theorem DAGCircuit.exists_fanoutTwo (C : DAGCircuit n) (hC : C.IsFaninTwo) :
    ∃ C' : DAGCircuit n, C'.IsFaninTwo ∧ C'.HasFanoutTwo ∧ (∀ x, C'.eval x = C.eval x) ∧
      C'.size ≤ 3 * C.size :=
  ⟨C.fanoutTwo hC, C.fanoutTwo_isFaninTwo hC, C.fanoutTwo_hasFanoutTwo hC,
    C.fanoutTwo_eval hC, (C.fanoutTwo_size_le hC).trans (by simp [DAGCircuit.size]; omega)⟩

end BoolCircuit
