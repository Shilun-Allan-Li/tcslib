/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.DAGTransform

/-!
# Fan-in reduction and De Morgan normalization of DAG circuits

Two instances of the gate-rewriting pass of `DAGTransform.lean`.

* `BoolCircuit.DAGCircuit.binarize` replaces every `∧`/`∨` gate of fan-in `k` by a
  balanced tree of fan-in-two gates (depth `⌈log₂ k⌉`).  The result has fan-in two, size at
  most `n + #gates * (size + 2)`, and depth at most `(⌈log₂ K⌉ + 1) * depth` for fan-in
  bound `K`.  [AB09, p. 118] uses this to show `AC^i ⊆ NC^{i+1}`.
* `BoolCircuit.DAGCircuit.deMorgan` replaces every `∨` gate by `¬ ∧ ¬`, leaving only `∧`
  and `¬` gates (the layered model's standard basis), at most tripling depth.

## Main definitions

* `BoolCircuit.emitTree` — a balanced tree of fan-in-two gates over a list of vertices.
* `BoolCircuit.DAGCircuit.binarize`, `BoolCircuit.DAGCircuit.deMorgan`.

## Main results

* `BoolCircuit.DAGCircuit.binarize_eval`, `binarize_isFaninTwo`, `binarize_size_le`,
  `binarize_depth_le`.
* `BoolCircuit.DAGCircuit.deMorgan_eval`, `deMorgan_isWellFormed`, `deMorgan_kind_ne_or`,
  `deMorgan_size_le`, `deMorgan_depth_le`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.7.1, p. 118.)
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

variable {n : ℕ}

/-! ## Gate-value algebra for `∧` and `∨` -/

/-- The binary operation of an `∧` or `∨` gate. -/
def GateKind.op : GateKind → Bool → Bool → Bool
  | .and => (· && ·)
  | .or => (· || ·)
  | .not => fun a _ => !a

/-- For an `∧` or `∨` gate of kind `k`, reading the concatenated input list `l₁ ++ l₂`
yields the binary operation `k.op` applied to the values of the gates reading `l₁` and `l₂`
separately (evaluated against the same vertex-value list). -/
theorem DAGGate.eval_append {k : GateKind} (hk : k ≠ .not) (l₁ l₂ : List ℕ)
    (vals : List Bool) :
    (⟨k, l₁ ++ l₂⟩ : DAGGate).eval vals =
      k.op ((⟨k, l₁⟩ : DAGGate).eval vals) ((⟨k, l₂⟩ : DAGGate).eval vals) := by
  cases k <;> simp_all [DAGGate.eval, GateKind.op, List.all_append, List.any_append]

/-- An `∧` or `∨` gate of kind `k` with exactly the two inputs `a`, `b` evaluates to
`k.op` of the values of vertices `a` and `b` (missing vertices read as `false`). -/
theorem DAGGate.eval_pair {k : GateKind} (hk : k ≠ .not) (a b : ℕ) (vals : List Bool) :
    (⟨k, [a, b]⟩ : DAGGate).eval vals = k.op (vals.getD a false) (vals.getD b false) := by
  cases k <;> simp_all [DAGGate.eval, GateKind.op]

/-- An `∧` or `∨` gate with a single input `a` simply returns the value of vertex `a`
(missing vertices read as `false`). -/
theorem DAGGate.eval_singleton {k : GateKind} (hk : k ≠ .not) (a : ℕ) (vals : List Bool) :
    (⟨k, [a]⟩ : DAGGate).eval vals = vals.getD a false := by
  cases k <;> simp_all [DAGGate.eval]

/-- Removing duplicate inputs does not change the value of an `∧` or `∨` gate: the gate
reading `l.dedup` evaluates to the same bit as the gate reading `l`. -/
theorem DAGGate.eval_dedup {k : GateKind} (hk : k ≠ .not) (l : List ℕ) (vals : List Bool) :
    (⟨k, l.dedup⟩ : DAGGate).eval vals = (⟨k, l⟩ : DAGGate).eval vals := by
  cases k
  · simp only [DAGGate.eval]; rw [Bool.eq_iff_iff]; simp [List.all_eq_true, List.mem_dedup]
  · simp only [DAGGate.eval]; rw [Bool.eq_iff_iff]; simp [List.any_eq_true, List.mem_dedup]
  · exact absurd rfl hk

private theorem foldr_max_le₂ {l : List ℕ} {f : ℕ → ℕ} {B : ℕ} (h : ∀ a ∈ l, f a ≤ B) :
    (l.map f).foldr max 0 ≤ B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

private theorem le_foldr_max₂ {l : List ℕ} {f : ℕ → ℕ} {a : ℕ} (ha : a ∈ l) :
    f a ≤ (l.map f).foldr max 0 := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp ha with rfl | ha
    · exact le_max_left _ _
    · exact (ih ha).trans (le_max_right _ _)

/-! ## Balanced trees of fan-in-two gates -/

/-- The number of gates of `emitTree` over `k` leaves: one constant gate when `k = 0`. -/
def treeCost (k : ℕ) : ℕ := if k = 0 then 1 else k - 1

/-- Emit a balanced tree of fan-in-two `k`-gates over the vertices `vs`, after `gs`;
returns the root.  No leaf: one fan-in-zero gate (a constant).  One leaf: that vertex. -/
def emitTree (n : ℕ) (k : GateKind) : List ℕ → List DAGGate → List DAGGate × ℕ
  | [], gs => (gs ++ [⟨k, []⟩], n + gs.length)
  | [v], gs => (gs, v)
  | a :: b :: rest, gs =>
    let r1 := emitTree n k ((a :: b :: rest).take ((rest.length + 2) / 2)) gs
    let r2 := emitTree n k ((a :: b :: rest).drop ((rest.length + 2) / 2)) r1.1
    (r2.1 ++ [⟨k, [r1.2, r2.2].dedup⟩], n + r2.1.length)
termination_by vs => vs.length
decreasing_by all_goals (simp only [List.length_take, List.length_drop, List.length_cons]; omega)

/-- What `emitTree` guarantees. -/
structure TreeSpec (n : ℕ) (k : GateKind) (vs : List ℕ) (gs : List DAGGate)
    (r : List DAGGate × ℕ) : Prop where
  extends_gates : ∃ ext, r.1 = gs ++ ext
  acyclic : GatesAcyclic n r.1
  vertex_lt : r.2 < n + r.1.length
  value : ∀ x : Fin n → Bool,
    vertexValue r.1 x r.2 = (⟨k, vs⟩ : DAGGate).eval (runWith DAGGate.eval gs (List.ofFn x))
  length_le : r.1.length ≤ gs.length + treeCost vs.length
  depth_le : vertexDepth n r.1 r.2 ≤
    Nat.clog 2 vs.length + 1 + (vs.map (vertexDepth n gs)).foldr max 0
  new_gates : ∀ h ∈ r.1.drop gs.length, h.kind = k ∧ h.args.Nodup ∧ h.args.length ≤ 2

/-- Correctness of `emitTree`: for an `∧`/`∨` kind `k`, if `gs` is acyclic and every vertex of
`vs` already exists, then emitting the balanced fan-in-two `k`-tree over `vs` after `gs`
satisfies `TreeSpec` — it only appends to `gs`, stays acyclic, returns an existing vertex whose
value is the fan-in-`|vs|` `k`-gate over `vs`, adds at most `treeCost |vs|` gates, raises the
depth by at most `⌈log₂ |vs|⌉ + 1` over the deepest input, and every new gate is a `k`-gate
with at most two distinct inputs.  [AB09, §6.7.1, p. 118]

**Proof sketch.** Strong induction on `|vs|`.  With no leaf a single constant `k`-gate is
emitted; with one leaf the leaf itself is returned and nothing is emitted.  Otherwise split
`vs` into its first half and second half, build the two subtrees recursively (the second after
the first), and append one `k`-gate reading both roots.  Its value is `k.op` of the two
half-gates, which by associativity of `∧`/`∨` over concatenation is the gate over all of `vs`.
The gate count is `treeCost` of each half plus one.  For depth, each half has length at most
`⌈|vs|/2⌉`, so its tree has depth at most `⌈log₂ ⌈|vs|/2⌉⌉ + 1 = ⌈log₂ |vs|⌉` over its inputs,
and the new root adds one more level. -/
theorem emitTree_spec (k : GateKind) (hk : k ≠ .not) :
    ∀ (vs : List ℕ) (gs : List DAGGate), GatesAcyclic n gs → (∀ v ∈ vs, v < n + gs.length) →
      TreeSpec n k vs gs (emitTree n k vs gs)
  | [], gs, hgs, hvs => by
    rw [emitTree]
    refine ⟨⟨_, rfl⟩, hgs.snoc (by simp), by simp, fun x => vertexValue_last _ _ _,
      by simp [treeCost], ?_, ?_⟩
    · rw [vertexDepth_last]; simp [DAGGate.depth]
    · intro h hh; simp at hh; subst hh; simp
  | [v], gs, hgs, hvs => by
    rw [emitTree]
    refine ⟨⟨[], by simp⟩, hgs, by simpa using hvs v (by simp), fun x => ?_,
      by simp [treeCost], by simp, by simp⟩
    rw [DAGGate.eval_singleton hk]; rfl
  | a :: b :: rest, gs, hgs, hvs => by
    set m := (rest.length + 2) / 2 with hm
    set vs := a :: b :: rest with hvsdef
    have hlen : vs.length = rest.length + 2 := by simp [hvsdef]
    have h1 := emitTree_spec k hk (vs.take m) gs hgs fun v hv => hvs v (List.mem_of_mem_take hv)
    set r1 := emitTree n k (vs.take m) gs with hr1
    obtain ⟨e1, he1⟩ := h1.extends_gates
    have h2 := emitTree_spec k hk (vs.drop m) r1.1 h1.acyclic fun v hv =>
      lt_of_lt_of_le (hvs v (List.mem_of_mem_drop hv)) (by rw [he1]; simp)
    set r2 := emitTree n k (vs.drop m) r1.1 with hr2
    obtain ⟨e2, he2⟩ := h2.extends_gates
    set g : DAGGate := ⟨k, [r1.2, r2.2].dedup⟩ with hg
    have hres : emitTree n k vs gs = (r2.1 ++ [g], n + r2.1.length) := by
      rw [hvsdef, emitTree]
    rw [hres]
    have hr1lt : r1.2 < n + r2.1.length := lt_of_lt_of_le h1.vertex_lt (by rw [he2]; simp)
    have htake_len : (vs.take m).length = m := by rw [List.length_take]; omega
    have hdrop_len : (vs.drop m).length = rest.length + 2 - m := by rw [List.length_drop]; omega
    refine ⟨⟨e1 ++ e2 ++ [g], by rw [he2, he1]; simp⟩, h2.acyclic.snoc ?_, by simp, ?_, ?_,
      ?_, ?_⟩
    · intro c hc
      have hc' : c ∈ [r1.2, r2.2] := List.mem_dedup.mp hc
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc'
      rcases hc' with rfl | rfl
      · exact hr1lt
      · exact h2.vertex_lt
    · intro x
      rw [vertexValue_last, hg, DAGGate.eval_dedup hk, DAGGate.eval_pair hk]
      have hv1 : (runWith DAGGate.eval r2.1 (List.ofFn x)).getD r1.2 false =
          (⟨k, vs.take m⟩ : DAGGate).eval (runWith DAGGate.eval gs (List.ofFn x)) := by
        have := h1.value x
        rw [← this, he2]
        exact vertexValue_append _ _ _ h1.vertex_lt
      have hv2 : (runWith DAGGate.eval r2.1 (List.ofFn x)).getD r2.2 false =
          (⟨k, vs.drop m⟩ : DAGGate).eval (runWith DAGGate.eval gs (List.ofFn x)) := by
        have := h2.value x
        rw [show (runWith DAGGate.eval r2.1 (List.ofFn x)).getD r2.2 false =
          vertexValue r2.1 x r2.2 from rfl, this, he1]
        apply DAGGate.eval_congr
        intro c hc
        exact vertexValue_append gs e1 x (hvs c (List.mem_of_mem_drop hc))
      rw [hv1, hv2, ← DAGGate.eval_append hk, List.take_append_drop]
    · have := h1.length_le; have := h2.length_le
      simp only [List.length_append, List.length_singleton]
      rw [htake_len] at *; rw [hdrop_len] at *
      simp only [treeCost, hlen] at *
      split_ifs at * <;> omega
    · rw [vertexDepth_last, hg, DAGGate.depth]
      dsimp only
      set M := (vs.map (vertexDepth n gs)).foldr max 0 with hM
      have hclog : Nat.clog 2 vs.length = Nat.clog 2 ((vs.length + 1) / 2) + 1 := by
        rw [Nat.clog_of_two_le (by norm_num) (by omega),
          show vs.length + 2 - 1 = vs.length + 1 by omega]
      have hc1 : Nat.clog 2 (vs.take m).length ≤ Nat.clog 2 ((vs.length + 1) / 2) :=
        Nat.clog_mono_right _ (by rw [htake_len]; omega)
      have hc2 : Nat.clog 2 (vs.drop m).length ≤ Nat.clog 2 ((vs.length + 1) / 2) :=
        Nat.clog_mono_right _ (by rw [hdrop_len]; omega)
      have hM1 : ((vs.take m).map (vertexDepth n gs)).foldr max 0 ≤ M :=
        foldr_max_le₂ fun c hc => le_foldr_max₂ (f := vertexDepth n gs)
          (List.mem_of_mem_take hc)
      have hM2 : ((vs.drop m).map (vertexDepth n r1.1)).foldr max 0 ≤ M :=
        foldr_max_le₂ fun c hc => by
          rw [he1, vertexDepth_append _ _ (hvs c (List.mem_of_mem_drop hc))]
          exact le_foldr_max₂ (f := vertexDepth n gs) (List.mem_of_mem_drop hc)
      have hd1 : vertexDepth n r2.1 r1.2 ≤ Nat.clog 2 vs.length + M := by
        rw [he2, vertexDepth_append _ _ h1.vertex_lt]
        have := h1.depth_le; omega
      have hd2 : vertexDepth n r2.1 r2.2 ≤ Nat.clog 2 vs.length + M := by
        have := h2.depth_le; omega
      have : (([r1.2, r2.2].dedup).map fun c =>
          (runWith DAGGate.depth r2.1 (List.replicate n 0)).getD c 0).foldr max 0 ≤
            Nat.clog 2 vs.length + M := by
        apply foldr_max_le₂
        intro c hc
        have hc' : c ∈ [r1.2, r2.2] := List.mem_dedup.mp hc
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc'
        rcases hc' with rfl | rfl
        · exact hd1
        · exact hd2
      omega
    · intro h hh
      have hsplit : (r2.1 ++ [g]).drop gs.length = e1 ++ e2 ++ [g] := by
        rw [he2, he1]; simp
      rw [hsplit, List.mem_append, List.mem_append, List.mem_singleton] at hh
      rcases hh with (hh | hh) | rfl
      · exact h1.new_gates h (by rw [he1]; simpa using hh)
      · exact h2.new_gates h (by rw [he2]; simpa using hh)
      · refine ⟨rfl, List.nodup_dedup _, ?_⟩
        exact (List.dedup_sublist _).length_le.trans (by simp)
termination_by vs => vs.length
decreasing_by all_goals (simp only [List.length_take, List.length_drop, List.length_cons]; omega)

/-! ## Binarization -/

/-- The binarization gadget: a `¬` gate is copied; an `∧`/`∨` gate becomes a balanced
tree over its (deduplicated) inputs. -/
def binarizeGadget (n : ℕ) (g : DAGGate) (gs : List DAGGate) : List DAGGate × ℕ :=
  match g.kind with
  | .not => (gs ++ [g], n + gs.length)
  | k => emitTree n k g.args.dedup gs

/-- The gate cost of a balanced tree over `k` leaves is at most `k + 2`. -/
theorem treeCost_le (k : ℕ) : treeCost k ≤ k + 2 := by unfold treeCost; split_ifs <;> omega

/-- The `∧`/`∨` case of the binarization gadget: for an `∧`/`∨` gate of kind `k` with at most
`K` existing inputs, the gadget meets `GadgetSpec` with depth increase `⌈log₂ K⌉ + 1`, cost
fan-in plus two, and every new gate of fan-in two.

**Proof sketch.** On an `∧`/`∨` gate the gadget is `emitTree` over the deduplicated inputs, so
all fields come from `emitTree_spec`: the value agrees because deduplication does not change an
`∧`/`∨` gate; the cost `treeCost` of the deduplicated list is at most fan-in plus two; the
depth bound follows because the deduplicated list is no longer than `K` (so `⌈log₂⌉` is
monotone) and its deepest input is among the original inputs; and each new `k`-gate has
distinct inputs, at most two of them, and is not a `¬` gate. -/
theorem binarizeGadget_andor (k : GateKind) (hk : k ≠ .not) (K : ℕ) (args : List ℕ)
    (gs : List DAGGate) (hgs : GatesAcyclic n gs) (hargs : ∀ a ∈ args, a < n + gs.length)
    (hK : args.length ≤ K) :
    GadgetSpec n (Nat.clog 2 K + 1) ((⟨k, args⟩ : DAGGate).args.length + 2) DAGGate.FaninTwo
      ⟨k, args⟩ gs (binarizeGadget n ⟨k, args⟩ gs) := by
  have hred : binarizeGadget n ⟨k, args⟩ gs = emitTree n k args.dedup gs := by
    cases k <;> first | exact absurd rfl hk | rfl
  rw [hred]
  have h := emitTree_spec k hk args.dedup gs hgs fun v hv => hargs v (List.mem_dedup.mp hv)
  have hdl : args.dedup.length ≤ args.length := (List.dedup_sublist _).length_le
  refine ⟨h.extends_gates, h.acyclic, h.vertex_lt, fun x => ?_, ?_, ?_, ?_⟩
  · rw [h.value x, DAGGate.eval_dedup hk]
  · have := h.length_le; have := treeCost_le args.dedup.length
    simp only; omega
  · refine h.depth_le.trans ?_
    have hc : Nat.clog 2 args.dedup.length ≤ Nat.clog 2 K := Nat.clog_mono_right _ (by omega)
    have hM : (args.dedup.map (vertexDepth n gs)).foldr max 0 ≤
        (args.map (vertexDepth n gs)).foldr max 0 :=
      foldr_max_le₂ fun a ha => le_foldr_max₂ (f := vertexDepth n gs) (List.mem_dedup.mp ha)
    simp only; omega
  · intro g hg
    obtain ⟨hkind, hnd, hlen⟩ := h.new_gates g hg
    exact ⟨⟨hnd, fun hn => absurd (hkind ▸ hn) hk⟩, hlen⟩

/-- The binarization gadget is a correct gadget (in the sense of `GadgetCorrect`) with depth
factor `⌈log₂ K⌉ + 1`: on every gate whose fan-in is at most `K` (and exactly one for `¬`),
it emits only fan-in-two gates computing the same value, at cost at most fan-in plus two.
[AB09, §6.7.1, p. 118]

**Proof sketch.** Case on the gate kind.  A `¬` gate (with exactly one input) is copied
unchanged: one new gate, depth increased by one, and it trivially has fan-in two.  An `∧` or
`∨` gate is handled by `binarizeGadget_andor`, the balanced-tree case. -/
theorem binarizeGadget_correct (K : ℕ) :
    GadgetCorrect n (Nat.clog 2 K + 1)
      (fun k l => (k = .not → l = 1) ∧ l ≤ K) DAGGate.FaninTwo (binarizeGadget n) := by
  intro g gs hgs hargs ⟨hnot, hK⟩
  rcases g with ⟨k, args⟩
  cases k
  case not =>
    have hl := hnot rfl
    refine ⟨⟨_, rfl⟩, hgs.snoc hargs, by simp [binarizeGadget], fun x => ?_, by
      simp [binarizeGadget], ?_, ?_⟩
    · exact vertexValue_last _ _ _
    · simp only [binarizeGadget]
      rw [vertexDepth_last]
      simp only [DAGGate.depth]
      have hmap : (args.map fun a => (runWith DAGGate.depth gs (List.replicate n 0)).getD a 0
          ).foldr max 0 = (args.map (vertexDepth n gs)).foldr max 0 := rfl
      omega
    · intro h hh
      simp only [binarizeGadget, List.drop_left', List.mem_singleton] at hh
      subst hh
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hl
      exact ⟨⟨List.nodup_singleton _, fun _ => rfl⟩, by simp⟩
  all_goals
    exact binarizeGadget_andor _ (by simp) K args gs hgs hargs hK

/-- In a well-formed circuit a gate reads distinct earlier vertices, so at most `size`. -/
theorem DAGCircuit.args_length_le_size (C : DAGCircuit n) (hwf : C.IsWellFormed) :
    ∀ g ∈ C.gates, g.args.length ≤ C.size := by
  intro g hg
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  have hnd := (hwf _ hg).1
  rw [← List.toFinset_card_of_nodup hnd]
  calc (C.gates[i]).args.toFinset.card ≤ (Finset.range C.size).card :=
        Finset.card_le_card fun a ha => by
          have := C.args_lt i hi a (List.mem_toFinset.mp ha)
          simp only [Finset.mem_range, DAGCircuit.size]; omega
    _ = C.size := Finset.card_range _

/-- Binarize a well-formed circuit: every `∧`/`∨` gate becomes a balanced tree of fan-in-two
gates.  [AB09, p. 118] -/
def DAGCircuit.binarize (C : DAGCircuit n) (hwf : C.IsWellFormed) : DAGCircuit n :=
  C.rewrite (binarizeGadget n) (binarizeGadget_correct C.size)
    fun g hg => ⟨(hwf g hg).2, C.args_length_le_size hwf g hg⟩

section Binarize

variable (C : DAGCircuit n) (hwf : C.IsWellFormed)

/-- Binarization preserves the function computed: on every input `x`, the binarized circuit
outputs the same bit as `C`.  [AB09, §6.7.1, p. 118] -/
theorem DAGCircuit.binarize_eval (x : Fin n → Bool) : (C.binarize hwf).eval x = C.eval x :=
  C.rewrite_eval _ _ _ x

/-- The binarized circuit has fan-in two: every gate is well formed and reads at most two
inputs.  [AB09, §6.7.1, p. 118] -/
theorem DAGCircuit.binarize_isFaninTwo : (C.binarize hwf).IsFaninTwo :=
  ⟨fun g hg => (C.rewrite_new_gates _ _ _ g hg).1, fun g hg => (C.rewrite_new_gates _ _ _ g hg).2⟩

/-- Each gate costs at most its fan-in plus two, and fan-in is at most `size`. -/
theorem DAGCircuit.binarize_size_le :
    (C.binarize hwf).size ≤ n + C.gates.length * (C.size + 2) := by
  have h1 := C.rewrite_length_le _ (binarizeGadget_correct C.size)
    fun g hg => ⟨(hwf g hg).2, C.args_length_le_size hwf g hg⟩
  have h2 := C.sum_cost_le (C.args_length_le_size hwf)
  simp only [DAGCircuit.size, DAGCircuit.binarize] at h1 h2 ⊢
  omega

/-- Depth is multiplied by at most `⌈log₂ size⌉ + 1`. -/
theorem DAGCircuit.binarize_depth_le :
    (C.binarize hwf).depth ≤ (Nat.clog 2 C.size + 1) * C.depth :=
  C.rewrite_depth_le _ _ _

end Binarize

/-! ## De Morgan normalization -/

/-- Emit `¬ a` for each vertex `a` of `as`, in order, after `gs`; returns the new vertices. -/
def emitNots (n : ℕ) : List ℕ → List DAGGate → List DAGGate × List ℕ
  | [], gs => (gs, [])
  | a :: as, gs =>
    let r := emitNots n as (gs ++ [⟨.not, [a]⟩])
    (r.1, (n + gs.length) :: r.2)

/-- What `emitNots` guarantees. -/
structure NotsSpec (n : ℕ) (as : List ℕ) (gs : List DAGGate) (r : List DAGGate × List ℕ) :
    Prop where
  extends_gates : ∃ ext, r.1 = gs ++ ext
  acyclic : GatesAcyclic n r.1
  length_eq : r.1.length = gs.length + as.length
  vertices_length : r.2.length = as.length
  vertex_lt : ∀ v ∈ r.2, v < n + r.1.length
  vertex_ge : ∀ v ∈ r.2, n + gs.length ≤ v
  nodup : r.2.Nodup
  value : ∀ x : Fin n → Bool, (r.2.map fun v => vertexValue r.1 x v) =
    as.map fun a => !vertexValue gs x a
  depth_le : ∀ v ∈ r.2, vertexDepth n r.1 v ≤ 1 + (as.map (vertexDepth n gs)).foldr max 0
  new_gates : ∀ h ∈ r.1.drop gs.length, h.WellFormed ∧ h.kind = .not

/-- Correctness of `emitNots`: if `gs` is acyclic and every vertex of `as` exists, then
appending one `¬` gate per element of `as` satisfies `NotsSpec` — exactly `|as|` new gates,
all well-formed `¬` gates, returning `|as|` distinct fresh vertices whose values are the
negations of the values of `as` (in order) and whose depths exceed the deepest vertex of `as`
by at most one.

**Proof sketch.** Induction on `as`.  For `a :: as`, append the gate `¬ a` (its input exists,
so acyclicity is preserved) and recurse on `as` after it.  The first returned vertex is the new
gate, which is fresh (index `n + |gs|`) and evaluates to `¬ a`; its depth is one more than that
of `a`.  The remaining vertices come from the induction hypothesis; since all of them lie at or
after index `n + |gs| + 1`, they are distinct from the new one, and appending gates does not
change the value or depth of previously existing vertices. -/
theorem emitNots_spec : ∀ (as : List ℕ) (gs : List DAGGate), GatesAcyclic n gs →
    (∀ a ∈ as, a < n + gs.length) → NotsSpec n as gs (emitNots n as gs)
  | [], gs, hgs, _ => ⟨⟨[], by simp [emitNots]⟩, by simpa [emitNots] using hgs,
      by simp [emitNots], by simp [emitNots], by simp [emitNots], by simp [emitNots],
      by simp [emitNots], fun x => by simp [emitNots], by simp [emitNots], by simp [emitNots]⟩
  | a :: as, gs, hgs, has => by
    set g : DAGGate := ⟨.not, [a]⟩ with hg
    have hgs' : GatesAcyclic n (gs ++ [g]) := hgs.snoc (by simpa [hg] using has a (by simp))
    have h := emitNots_spec as (gs ++ [g]) hgs' fun b hb =>
      lt_of_lt_of_le (has b (by simp [hb])) (by simp)
    set r := emitNots n as (gs ++ [g]) with hr
    have hres : emitNots n (a :: as) gs = (r.1, (n + gs.length) :: r.2) := rfl
    rw [hres]
    obtain ⟨e, he⟩ := h.extends_gates
    have hglt : n + gs.length < n + r.1.length := by rw [he]; simp
    refine ⟨⟨g :: e, by rw [he]; simp⟩, h.acyclic, by rw [h.length_eq]; simp; omega,
      by simp [h.vertices_length], ?_, ?_, ?_, fun x => ?_, ?_, ?_⟩
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hglt
      · exact h.vertex_lt v hv
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact le_refl _
      · exact le_trans (by simp : n + gs.length ≤ n + (gs ++ [g]).length) (h.vertex_ge v hv)
    · refine List.nodup_cons.mpr ⟨fun hmem => ?_, h.nodup⟩
      have := h.vertex_ge _ hmem; simp at this
    · simp only [List.map_cons]
      congr 1
      · rw [he, vertexValue_append _ _ _ (by simp), vertexValue_last]
        simp [hg, DAGGate.eval, vertexValue]
      · rw [h.value x]
        exact List.map_congr_left fun b hb => by
          rw [vertexValue_append _ _ _ (has b (by simp [hb]))]
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · rw [he, vertexDepth_append _ _ (by simp), vertexDepth_last]
        simp only [hg, DAGGate.depth, List.map_cons, List.map_nil, List.foldr_cons,
          List.foldr_nil, max_eq_left (Nat.zero_le _)]
        have := le_foldr_max₂ (f := vertexDepth n gs) (l := a :: as) (a := a) (by simp)
        simp only [vertexDepth] at this ⊢
        omega
      · refine (h.depth_le v hv).trans ?_
        have : (as.map (vertexDepth n (gs ++ [g]))).foldr max 0 ≤
            ((a :: as).map (vertexDepth n gs)).foldr max 0 :=
          foldr_max_le₂ fun b hb => by
            rw [vertexDepth_append _ _ (has b (by simp [hb]))]
            exact le_foldr_max₂ (f := vertexDepth n gs) (by simp [hb])
        omega
    · intro h' hh
      have hsplit : r.1.drop gs.length = g :: e := by rw [he]; simp
      rw [hsplit, List.mem_cons] at hh
      rcases hh with rfl | hh
      · exact ⟨⟨List.nodup_singleton _, fun _ => by simp [hg]⟩, rfl⟩
      · exact h.new_gates h' (by rw [he]; simpa using hh)

/-- The De Morgan gadget: `∨` becomes `¬ ∧ ¬`; `∧` and `¬` are copied (the `∧` with its
inputs deduplicated). -/
def deMorganGadget (n : ℕ) (g : DAGGate) (gs : List DAGGate) : List DAGGate × ℕ :=
  match g.kind with
  | .or =>
    let r := emitNots n g.args.dedup gs
    let gs2 := r.1 ++ [⟨.and, r.2⟩]
    (gs2 ++ [⟨.not, [n + r.1.length]⟩], n + gs2.length)
  | .and => (gs ++ [⟨.and, g.args.dedup⟩], n + gs.length)
  | .not => (gs ++ [g], n + gs.length)

/-- Gates of a De Morgan-normal circuit: well formed, no `∨`, fan-in at most `max 1 K`. -/
def DAGGate.NoOr (K : ℕ) (g : DAGGate) : Prop :=
  g.WellFormed ∧ g.kind ≠ .or ∧ g.args.length ≤ max 1 K

/-- The De Morgan gadget is a correct gadget (in the sense of `GadgetCorrect`) with depth
factor `3`: on every gate whose fan-in is at most `K` (exactly one for `¬`), it emits only
well-formed non-`∨` gates of fan-in at most `max 1 K` computing the same value, at cost at
most fan-in plus two.

**Proof sketch.** Case on the gate kind.  An `∧` gate is copied with deduplicated inputs
(same value, depth increase one).  A `¬` gate is copied unchanged.  An `∨` gate over inputs
`a₁,…,a_k` becomes `¬(¬a₁ ∧ ⋯ ∧ ¬a_k)` over the deduplicated inputs: `emitNots_spec` supplies
the `k` negations, then one `∧` gate over them and one final `¬` gate are appended.  By
De Morgan's law its value is `a₁ ∨ ⋯ ∨ a_k`; it uses `k + 2` gates and has depth at most three
more than the deepest input. -/
theorem deMorganGadget_correct (K : ℕ) :
    GadgetCorrect n 3 (fun k l => (k = .not → l = 1) ∧ l ≤ K) (DAGGate.NoOr K)
      (deMorganGadget n) := by
  intro g gs hgs hargs ⟨hnot, hK⟩
  rcases g with ⟨k, args⟩
  cases k
  case and =>
    refine ⟨⟨_, rfl⟩, hgs.snoc fun a ha => hargs a (List.mem_dedup.mp ha), by
      simp [deMorganGadget], fun x => ?_, by simp [deMorganGadget], ?_, ?_⟩
    · simp only [deMorganGadget]
      rw [vertexValue_last, DAGGate.eval_dedup (by simp)]
    · simp only [deMorganGadget]
      rw [vertexDepth_last]
      simp only [DAGGate.depth]
      have : (args.dedup.map fun a => (runWith DAGGate.depth gs (List.replicate n 0)).getD a 0
          ).foldr max 0 ≤ (args.map (vertexDepth n gs)).foldr max 0 :=
        foldr_max_le₂ fun a ha => le_foldr_max₂ (f := vertexDepth n gs) (List.mem_dedup.mp ha)
      omega
    · intro h hh
      simp only [deMorganGadget, List.drop_left', List.mem_singleton] at hh
      subst hh
      refine ⟨⟨List.nodup_dedup _, fun h => by simp at h⟩, by simp, ?_⟩
      have := (List.dedup_sublist args).length_le; simp only at hK ⊢; omega
  case not =>
    have hl := hnot rfl
    refine ⟨⟨_, rfl⟩, hgs.snoc hargs, by simp [deMorganGadget], fun x => ?_, by
      simp [deMorganGadget], ?_, ?_⟩
    · simp only [deMorganGadget]; exact vertexValue_last _ _ _
    · simp only [deMorganGadget]
      rw [vertexDepth_last]
      simp only [DAGGate.depth]
      have hmap : (args.map fun a => (runWith DAGGate.depth gs (List.replicate n 0)).getD a 0
          ).foldr max 0 = (args.map (vertexDepth n gs)).foldr max 0 := rfl
      omega
    · intro h hh
      simp only [deMorganGadget, List.drop_left', List.mem_singleton] at hh
      subst hh
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hl
      exact ⟨⟨List.nodup_singleton _, fun _ => rfl⟩, by simp, by simp⟩
  case or =>
    have h := emitNots_spec args.dedup gs hgs fun a ha => hargs a (List.mem_dedup.mp ha)
    set r := emitNots n args.dedup gs with hr
    set gand : DAGGate := ⟨.and, r.2⟩ with hgand
    set gs2 := r.1 ++ [gand] with hgs2
    set gnot : DAGGate := ⟨.not, [n + r.1.length]⟩ with hgnot
    have hres : deMorganGadget n ⟨.or, args⟩ gs = (gs2 ++ [gnot], n + gs2.length) := rfl
    rw [hres]
    obtain ⟨e, he⟩ := h.extends_gates
    have hac2 : GatesAcyclic n gs2 := h.acyclic.snoc h.vertex_lt
    have hdl : args.dedup.length ≤ args.length := (List.dedup_sublist _).length_le
    refine ⟨⟨e ++ [gand, gnot], by rw [hgs2, he]; simp⟩, hac2.snoc (by simp [hgs2, hgnot]), by simp,
      fun x => ?_, ?_, ?_, ?_⟩
    · rw [vertexValue_last]
      simp only [hgnot, DAGGate.eval, List.all_cons, List.all_nil, Bool.and_true]
      have hand : (runWith DAGGate.eval gs2 (List.ofFn x)).getD (n + r.1.length) false =
          r.2.all fun v => vertexValue r.1 x v := by
        have := vertexValue_last r.1 gand x
        simp only [vertexValue] at this ⊢
        rw [this]; rfl
      rw [hand]
      have hv := h.value x
      have : (r.2.all fun v => vertexValue r.1 x v) =
          (args.dedup.map fun a => !vertexValue gs x a).all id := by
        rw [← hv, List.all_map]; rfl
      rw [this, List.all_map]
      rw [Bool.eq_iff_iff]
      simp [List.any_eq_true, List.mem_dedup, vertexValue]
    · have := h.length_eq
      simp only [hgs2, List.length_append, List.length_singleton]; omega
    · rw [vertexDepth_last]
      simp only [hgnot, DAGGate.depth, List.map_cons, List.map_nil, List.foldr_cons,
        List.foldr_nil, max_eq_left (Nat.zero_le _)]
      have hand : (runWith DAGGate.depth gs2 (List.replicate n 0)).getD (n + r.1.length) 0 =
          1 + (r.2.map (vertexDepth n r.1)).foldr max 0 := by
        have := vertexDepth_last (n := n) r.1 gand
        simp only [vertexDepth] at this ⊢
        rw [this]; rfl
      rw [hand]
      have : (r.2.map (vertexDepth n r.1)).foldr max 0 ≤
          1 + (args.map (vertexDepth n gs)).foldr max 0 :=
        foldr_max_le₂ fun v hv => (h.depth_le v hv).trans (by
          have : (args.dedup.map (vertexDepth n gs)).foldr max 0 ≤
              (args.map (vertexDepth n gs)).foldr max 0 :=
            foldr_max_le₂ fun a ha => le_foldr_max₂ (f := vertexDepth n gs)
              (List.mem_dedup.mp ha)
          omega)
      omega
    · intro h' hh
      have hsplit : (gs2 ++ [gnot]).drop gs.length = e ++ [gand, gnot] := by
        rw [hgs2, he]; simp
      rw [hsplit, List.mem_append] at hh
      rcases hh with hh | hh
      · obtain ⟨hwf, hkind⟩ := h.new_gates h' (by rw [he]; simpa using hh)
        refine ⟨hwf, by rw [hkind]; simp, ?_⟩
        obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (hwf.2 hkind)
        rw [ha]; simp
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hh
        rcases hh with rfl | rfl
        · refine ⟨⟨h.nodup, fun h => by simp [hgand] at h⟩, by simp [hgand], ?_⟩
          simp only [hgand, h.vertices_length]; simp only at hK; omega
        · exact ⟨⟨List.nodup_singleton _, fun _ => by simp [hgnot]⟩, by simp [hgnot],
            by simp [hgnot]⟩

/-- De Morgan normalization of a well-formed circuit: no `∨` gates remain. -/
def DAGCircuit.deMorgan (C : DAGCircuit n) (hwf : C.IsWellFormed) : DAGCircuit n :=
  C.rewrite (deMorganGadget n) (deMorganGadget_correct C.size)
    fun g hg => ⟨(hwf g hg).2, C.args_length_le_size hwf g hg⟩

section DeMorgan

variable (C : DAGCircuit n) (hwf : C.IsWellFormed)

/-- De Morgan normalization preserves the function computed: on every input `x`, the
normalized circuit outputs the same bit as `C`. -/
theorem DAGCircuit.deMorgan_eval (x : Fin n → Bool) : (C.deMorgan hwf).eval x = C.eval x :=
  C.rewrite_eval _ _ _ x

/-- The De Morgan-normalized circuit is well formed: every gate reads distinct inputs, and
every `¬` gate reads exactly one. -/
theorem DAGCircuit.deMorgan_isWellFormed : (C.deMorgan hwf).IsWellFormed :=
  fun g hg => (C.rewrite_new_gates _ _ _ g hg).1

/-- The De Morgan-normalized circuit contains no `∨` gate: every gate is `∧` or `¬`. -/
theorem DAGCircuit.deMorgan_kind_ne_or : ∀ g ∈ (C.deMorgan hwf).gates, g.kind ≠ .or :=
  fun g hg => (C.rewrite_new_gates _ _ _ g hg).2.1

/-- De Morgan normalization increases size to at most `n + #gates · (size + 2)`, since each
original gate is replaced by at most its fan-in plus two gates and fan-in is at most `size`. -/
theorem DAGCircuit.deMorgan_size_le :
    (C.deMorgan hwf).size ≤ n + C.gates.length * (C.size + 2) := by
  have h1 := C.rewrite_length_le _ (deMorganGadget_correct C.size)
    fun g hg => ⟨(hwf g hg).2, C.args_length_le_size hwf g hg⟩
  have h2 := C.sum_cost_le (C.args_length_le_size hwf)
  simp only [DAGCircuit.size, DAGCircuit.deMorgan] at h1 h2 ⊢
  omega

/-- De Morgan normalization at most triples the depth of the circuit. -/
theorem DAGCircuit.deMorgan_depth_le : (C.deMorgan hwf).depth ≤ 3 * C.depth :=
  C.rewrite_depth_le _ _ _

end DeMorgan

end BoolCircuit
