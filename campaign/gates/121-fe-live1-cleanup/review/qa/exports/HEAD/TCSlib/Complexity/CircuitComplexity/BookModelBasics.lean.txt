/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.DAGFanin
import TCSlib.Complexity.CircuitComplexity.PPoly
import TCSlib.Complexity.CircuitComplexity.SizeClasses

/-!
# Basic size bounds in the book's circuit model

Three small facts from [AB09, §6.1] restated over the book's model
`BoolCircuit.DAGCircuit` ([AB09, Def 6.1]), with explicit constants.

* [AB09, Ex 6.3], first half: `{1ⁿ}` is decided by linear-size circuits — a balanced tree
  of fan-in-two `∧` gates over the inputs.
* [AB09, pp. 107–108]: "a `∨` or `∧` gate with fan-in `f` can be replaced with a subcircuit
  consisting of `f − 1` gates of fan-in `2`", stated for whole circuits: binarizing a
  well-formed circuit costs `max 1 (f − 1)` gates per gate of fan-in `f`.
* [AB09, p. 108] citing [AB09, Claim 2.13]: every `f : {0,1}ⁿ → {0,1}` has a fan-in-two
  circuit of size `n 2ⁿ + 2n + 1`.

## Main definitions

* `BoolCircuit.emitTrees` — one balanced fan-in-two tree (`emitTree`) per leaf list, with
  its specification `BoolCircuit.TreesSpec`.
* `BoolCircuit.andAllDAG`, `BoolCircuit.andAllFamily` — the `∧`-tree circuits for `{1ⁿ}`.
* `BoolCircuit.negInputGates`, `BoolCircuit.litVertex`, `BoolCircuit.mintermLeaves`,
  `BoolCircuit.dnfDAG` — the DNF circuit of a Boolean function.

## Main results

* `Language.allOnes_inSIZE_linear` — `{1ⁿ} ∈ SIZE(2n + 1)` ([AB09, Ex 6.3]); hence
  `Language.allOnes_inPPoly`.
* `BoolCircuit.DAGCircuit.binarize_size_le_sum`,
  `BoolCircuit.DAGCircuit.exists_faninTwo_size_le_sum` — fan-in reduction with the book's
  gate count ([AB09, pp. 107–108]).
* `BoolCircuit.exists_dagCircuit_faninTwo_size_le` — every function has a fan-in-two
  circuit of size `≤ n 2ⁿ + 2n + 1` ([AB09, Claim 2.13] as cited on p. 108).  The sharper
  `O(2ⁿ/n)` bound of [AB09, Ex 6.1] is `BoolCircuit.exists_dagCircuit_faninTwo_mul_size_le`
  (`Lupanov.lean`).

## Divergences from [AB09]

* **Sizes count inputs.**  [AB09, Def 6.1]'s size counts every vertex, so each bound
  carries the `n` input vertices: `{1ⁿ}` gets size `2n − 1` (`n` inputs, `n − 1` gates),
  bounded uniformly by `2n + 1` to cover the constant circuit at `n = 0`.
* **Fan-in `0` and `1`.**  The model allows constant (fan-in-`0`) and identity
  (fan-in-`1`) `∧`/`∨` gates (see `DAGCircuit.lean`); the fan-in-reduction count charges
  `max 1 (f − 1)`, i.e. one gate for a constant, where the book's `f − 1` would give `−1`.
* **DNF instead of CNF.**  [AB09, Claim 2.13] builds the CNF over the falsifying
  assignments; we build the dual DNF over the satisfying ones (see `Universal.lean`, whose
  tree-circuit version this complements).  The `2n + 1` beyond the book's `n 2ⁿ` is the
  `n` inputs, the `n` shared `¬` gates, and one gate for the degenerate cases.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1: pp. 107–108, Example 6.3; Claim 2.13.)
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

variable {n : ℕ}

/-! ## Emitting several balanced trees -/

/-- Emit one balanced fan-in-two `k`-tree (`emitTree`) per leaf list of `vss`, one after
another after `gs`; returns the gates and the roots. -/
def emitTrees (n : ℕ) (k : GateKind) : List (List ℕ) → List DAGGate → List DAGGate × List ℕ
  | [], gs => (gs, [])
  | vs :: vss, gs =>
    let r := emitTree n k vs gs
    let r' := emitTrees n k vss r.1
    (r'.1, r.2 :: r'.2)

/-- What `emitTrees` guarantees: it only appends, keeps acyclicity, root `j` computes the
`k`-gate over the `j`-th leaf list, and it adds `∑ treeCost |vs|` fan-in-two `k`-gates. -/
structure TreesSpec (n : ℕ) (k : GateKind) (vss : List (List ℕ)) (gs : List DAGGate)
    (r : List DAGGate × List ℕ) : Prop where
  extends_gates : ∃ ext, r.1 = gs ++ ext
  acyclic : GatesAcyclic n r.1
  length_eq : r.2.length = vss.length
  vertex_lt : ∀ v ∈ r.2, v < n + r.1.length
  value : ∀ x : Fin n → Bool, r.2.map (vertexValue r.1 x) =
    vss.map fun vs => (⟨k, vs⟩ : DAGGate).eval (runWith DAGGate.eval gs (List.ofFn x))
  length_le : r.1.length ≤ gs.length + (vss.map fun vs => treeCost vs.length).sum
  new_gates : ∀ h ∈ r.1.drop gs.length, h.kind = k ∧ h.args.Nodup ∧ h.args.length ≤ 2

/-- `emitTrees` meets `TreesSpec` when every leaf is an existing vertex.

**Proof sketch.** Induction on the leaf lists.  The first tree meets `TreeSpec`
(`emitTree_spec`); the remaining trees are emitted after it, and their leaves are still
existing vertices, so the induction hypothesis applies.  Values of the first root and of
all leaves are unchanged by appending gates (`vertexValue_append`, `runWith_getD_of_lt`),
lengths add, and the new gates are those of the first tree followed by the rest. -/
theorem emitTrees_spec (k : GateKind) (hk : k ≠ .not) :
    ∀ (vss : List (List ℕ)) (gs : List DAGGate), GatesAcyclic n gs →
      (∀ vs ∈ vss, ∀ v ∈ vs, v < n + gs.length) → TreesSpec n k vss gs (emitTrees n k vss gs)
  | [], gs, hgs, _ => by
    refine ⟨⟨[], by simp [emitTrees]⟩, hgs, rfl, by simp [emitTrees], fun x => by
      simp [emitTrees], by simp [emitTrees], by simp [emitTrees]⟩
  | vs :: vss, gs, hgs, hvs => by
    have h1 := emitTree_spec k hk vs gs hgs (hvs vs (by simp))
    obtain ⟨e1, he1⟩ := h1.extends_gates
    have hlen1 : gs.length ≤ (emitTree n k vs gs).1.length := by rw [he1]; simp
    have h2 := emitTrees_spec k hk vss (emitTree n k vs gs).1 h1.acyclic
      (fun ws hws v hv => lt_of_lt_of_le (hvs ws (by simp [hws]) v hv) (by omega))
    obtain ⟨e2, he2⟩ := h2.extends_gates
    have hdef : emitTrees n k (vs :: vss) gs = ((emitTrees n k vss (emitTree n k vs gs).1).1,
        (emitTree n k vs gs).2 :: (emitTrees n k vss (emitTree n k vs gs).1).2) := rfl
    rw [hdef]
    refine ⟨⟨e1 ++ e2, by rw [he2, he1, List.append_assoc]⟩, h2.acyclic,
      by simp [h2.length_eq], ?_, ?_, ?_, ?_⟩
    · intro v hv
      simp only [List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact lt_of_lt_of_le h1.vertex_lt (by rw [he2]; simp)
      · exact h2.vertex_lt v hv
    · intro x
      simp only [List.map_cons]
      rw [h2.value x, he2, vertexValue_append _ _ _ h1.vertex_lt, h1.value x]
      congr 1
      apply List.map_congr_left
      intro ws hws
      apply DAGGate.eval_congr
      intro a ha
      rw [he1, runWith_append, runWith_getD_of_lt]
      simpa using hvs ws (by simp [hws]) a ha
    · have := h1.length_le; have := h2.length_le
      simp only [List.map_cons, List.sum_cons]; omega
    · intro h hh
      rw [he2, he1, List.append_assoc, List.drop_left, List.mem_append] at hh
      rcases hh with hh | hh
      · exact h1.new_gates h (by rw [he1, List.drop_left]; exact hh)
      · exact h2.new_gates h (by rw [he2, List.drop_left]; exact hh)

/-! ## [AB09, Ex 6.3]: `{1ⁿ}` has linear-size circuits in the book's model -/

/-- The `n`-input circuit computing `x₁ ∧ ⋯ ∧ xₙ` by a balanced tree of fan-in-two `∧`
gates over the inputs (the constant `1`, one fan-in-zero `∧` gate, when `n = 0`).
[AB09, Ex 6.3] -/
def andAllDAG (n : ℕ) : DAGCircuit n where
  gates := (emitTree n .and (List.range n) []).1
  output := (emitTree n .and (List.range n) []).2
  args_lt := (emitTree_spec .and (by decide) (List.range n) [] GatesAcyclic.nil
    (by simp)).acyclic
  output_lt := (emitTree_spec .and (by decide) (List.range n) [] GatesAcyclic.nil
    (by simp)).vertex_lt

private theorem andAllDAG_spec (n : ℕ) :
    TreeSpec n .and (List.range n) [] (emitTree n .and (List.range n) []) :=
  emitTree_spec .and (by decide) (List.range n) [] GatesAcyclic.nil (by simp)

/-- `andAllDAG n` outputs `1` exactly on the all-ones input. -/
theorem andAllDAG_eval (x : Fin n → Bool) : (andAllDAG n).eval x = true ↔ ∀ i, x i = true := by
  have h := (andAllDAG_spec n).value x
  change vertexValue (andAllDAG n).gates x (andAllDAG n).output = _ at h
  rw [DAGCircuit.eval, DAGCircuit.values]
  change vertexValue (andAllDAG n).gates x (andAllDAG n).output = true ↔ _
  rw [h]
  simp only [DAGGate.eval, runWith_nil, List.all_eq_true, List.mem_range]
  constructor
  · intro hall i
    have := hall i i.isLt
    simpa using this
  · intro hall a ha
    simpa [ha] using hall ⟨a, ha⟩

/-- `andAllDAG n` has fan-in two. -/
theorem andAllDAG_isFaninTwo : (andAllDAG n).IsFaninTwo := by
  have h := (andAllDAG_spec n).new_gates
  simp only [List.length_nil, List.drop_zero] at h
  refine ⟨fun g hg => ⟨(h g hg).2.1, fun hn => ?_⟩, fun g hg => (h g hg).2.2⟩
  have := (h g hg).1
  rw [this] at hn
  exact absurd hn (by decide)

/-- `andAllDAG n` has `max 1 (2n - 1)` vertices at most: `n` inputs and `n - 1` gates
(one constant gate when `n = 0`). -/
theorem andAllDAG_size_le : (andAllDAG n).size ≤ 2 * n + 1 := by
  have h := (andAllDAG_spec n).length_le
  simp only [List.length_nil, List.length_range, zero_add] at h
  have := treeCost_le n
  unfold treeCost at h
  simp only [DAGCircuit.size]
  change n + (emitTree n .and (List.range n) []).1.length ≤ 2 * n + 1
  split_ifs at h <;> omega

/-- The family `n ↦ andAllDAG n`. -/
def andAllFamily : DAGCircuitFamily := ⟨andAllDAG⟩

/-- `{1ⁿ : n ∈ ℕ}` has linear-size circuits in the book's model: it is in
`SIZE(2n + 1)`.  [AB09, Ex 6.3]

The book's circuit is "a tree of AND gates that computes the AND of all input bits"; with
fan-in two this is `n - 1` gates over the `n` inputs, so size `2n - 1` for `n ≥ 1`
(`2n + 1` covers the constant-`1` circuit of size `1` at `n = 0`). -/
theorem _root_.Language.allOnes_inSIZE_linear :
    Language.allOnes.InSIZE (fun n => 2 * n + 1) := by
  refine ⟨andAllFamily, fun m => andAllDAG_isFaninTwo, fun m => andAllDAG_size_le, ?_⟩
  ext w
  rw [DAGCircuitFamily.mem_language_iff]
  change (andAllDAG w.length).eval w.get = true ↔ ∀ b ∈ w, b = true
  rw [andAllDAG_eval]
  constructor
  · intro h b hb
    obtain ⟨i, rfl⟩ := List.get_of_mem hb
    exact h i
  · intro h i
    exact h _ (List.get_mem w i)

/-- `{1ⁿ} ∈ P/poly` for the book's `P/poly`: the linear bound `2n + 1` of
`allOnes_inSIZE_linear` is polynomial.  [AB09, Ex 6.3] -/
theorem _root_.Language.allOnes_inPPoly : Language.allOnes.InPPoly :=
  Language.allOnes_inSIZE_linear.inPPoly (a := 3) (k := 1) fun n => by rw [pow_one]; omega

/-! ## [AB09, pp. 107–108]: a fan-in-`f` gate costs `f - 1` fan-in-two gates -/

/-- A tree of `m ≤ k` leaves costs at most `max 1 (k - 1)` gates. -/
theorem treeCost_le_max {m k : ℕ} (h : m ≤ k) : treeCost m ≤ max 1 (k - 1) := by
  unfold treeCost; split_ifs <;> omega

/-- Binarizing a gate list costs at most `max 1 (f - 1)` new gates for each old gate of
fan-in `f`.

**Proof sketch.** Induction on the gate list from the right.  The binarization invariant
(`rewriteGates_inv`) gives that the gates so far are acyclic and every remapped input is an
existing vertex.  The last gate `g` adds one gate if it is a `¬` gate, and otherwise a
balanced tree over its at most `f` distinct remapped inputs, of at most `treeCost` of that
many leaves `≤ max 1 (f - 1)` gates (`emitTree_spec`, `treeCost_le_max`). -/
private theorem rewriteGates_binarize_length_le (K : ℕ) :
    ∀ old : List DAGGate, GatesAcyclic n old →
      (∀ g ∈ old, (g.kind = .not → g.args.length = 1) ∧ g.args.length ≤ K) →
      (rewriteGates n (binarizeGadget n) old).1.length ≤
        (old.map fun g => max 1 (g.args.length - 1)).sum := by
  intro old
  induction old using List.reverseRecOn with
  | nil => intro _ _; simp [rewriteGates]
  | append_singleton old g ih =>
    intro hac hQ
    have hac' : GatesAcyclic n old := fun i hi a ha => by
      have := hac i (by simp; omega) a (by rwa [List.getElem_append_left hi])
      exact this
    have hQ' : ∀ g' ∈ old, (g'.kind = .not → g'.args.length = 1) ∧ g'.args.length ≤ K :=
      fun g' hg' => hQ g' (by simp [hg'])
    have hinv := rewriteGates_inv (binarizeGadget_correct K) old hac' hQ'
    have ih' := ih hac' hQ'
    have hglt : ∀ a ∈ g.args, a < n + old.length := fun a ha => by
      have := hac old.length (by simp) a (by simpa using ha); exact this
    have hstep : rewriteGates n (binarizeGadget n) (old ++ [g]) =
        rewriteStep (binarizeGadget n) (rewriteGates n (binarizeGadget n) old) g := by
      simp [rewriteGates, List.foldl_append]
    rw [hstep]
    set s := rewriteGates n (binarizeGadget n) old with hs
    simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    suffices h : (rewriteStep (binarizeGadget n) s g).1.length ≤
        s.1.length + max 1 (g.args.length - 1) by omega
    have hmem : ∀ v ∈ (g.args.map fun a => s.2.getD a 0).dedup, v < n + s.1.length := by
      intro v hv
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hv)
      exact hinv.map_lt a (hglt a ha)
    have hdl : (g.args.map fun a => s.2.getD a 0).dedup.length ≤ g.args.length :=
      ((List.dedup_sublist _).length_le).trans (by simp)
    rcases g with ⟨k, args⟩
    dsimp only at hmem hdl ⊢
    cases k
    case not => simp [rewriteStep, binarizeGadget]
    case and =>
      have hspec := emitTree_spec .and (by decide) _ s.1 hinv.acyclic hmem
      have := hspec.length_le
      have := treeCost_le_max hdl
      simp only [rewriteStep, binarizeGadget]
      omega
    case or =>
      have hspec := emitTree_spec .or (by decide) _ s.1 hinv.acyclic hmem
      have := hspec.length_le
      have := treeCost_le_max hdl
      simp only [rewriteStep, binarizeGadget]
      omega

/-- Binarizing a well-formed circuit with unbounded fan-in gives at most
`n + ∑_g max 1 (fanin g - 1)` vertices: a `∧`/`∨` gate of fan-in `f ≥ 2` becomes `f - 1`
fan-in-two gates, a `¬` gate stays one gate, and a constant (fan-in `0`) stays one gate.
[AB09, pp. 107–108]

**Proof sketch.** The binarization pass (`DAGCircuit.binarize`) replaces each old gate in
turn: a `¬` gate is copied (one gate) and an `∧`/`∨` gate of fan-in `f` becomes a balanced
tree over its at most `f` distinct remapped inputs, which has at most `max 1 (f - 1)` gates
(`emitTree_spec`, `treeCost_le_max`).  Summing over the old gates by induction on the gate
list gives the bound. -/
theorem DAGCircuit.binarize_size_le_sum (C : DAGCircuit n) (hwf : C.IsWellFormed) :
    (C.binarize hwf).size ≤ n + (C.gates.map fun g => max 1 (g.args.length - 1)).sum := by
  have := rewriteGates_binarize_length_le C.size C.gates C.args_lt
    (fun g hg => ⟨(hwf g hg).2, C.args_length_le_size hwf g hg⟩)
  change n + (rewriteGates n (binarizeGadget n) C.gates).1.length ≤ _
  omega

/-- Unbounded fan-in is no more powerful than fan-in two, up to the book's gate count:
every well-formed circuit with `∧`/`∨` gates of any fan-in is equivalent to a fan-in-two
circuit with at most `n + ∑_g max 1 (fanin g - 1)` vertices — each `∧`/`∨` gate of fan-in
`f ≥ 2` replaced by `f - 1` gates of fan-in two, every other gate kept as one gate.
[AB09, pp. 107–108]

The book says "a `∨` or `∧` gate with fan-in `f` can be replaced with a subcircuit of
`f - 1` gates of fan-in `2`"; `max 1 (f - 1)` additionally charges one gate to a constant
(fan-in `0`) and to an identity gate (fan-in `1`, which in fact costs nothing). -/
theorem DAGCircuit.exists_faninTwo_size_le_sum (C : DAGCircuit n) (hwf : C.IsWellFormed) :
    ∃ C' : DAGCircuit n, C'.IsFaninTwo ∧ (∀ x, C'.eval x = C.eval x) ∧
      C'.size ≤ n + (C.gates.map fun g => max 1 (g.args.length - 1)).sum :=
  ⟨C.binarize hwf, C.binarize_isFaninTwo hwf, C.binarize_eval hwf,
    C.binarize_size_le_sum hwf⟩

/-! ## [AB09, Claim 2.13 as cited p. 108]: every function has a fan-in-two circuit of size
`O(n 2ⁿ)` -/

/-- The `n` shared negation gates `¬x₀, …, ¬x_{n-1}`, gate `k` at vertex `n + k`. -/
def negInputGates (n : ℕ) : List DAGGate := (List.range n).map fun k => ⟨.not, [k]⟩

/-- There are `n` negation gates. -/
@[simp] theorem length_negInputGates : (negInputGates n).length = n := by
  simp [negInputGates]

/-- The negation gates read only the inputs. -/
theorem negInputGates_acyclic : GatesAcyclic n (negInputGates n) := by
  intro i hi a ha
  simp only [negInputGates, List.getElem_map, List.getElem_range, List.mem_singleton] at ha
  subst ha
  simp only [length_negInputGates] at hi
  omega

/-- After the negation gates, vertex `n + i` holds `¬xᵢ`. -/
theorem vertexValue_negInputGates (x : Fin n → Bool) (i : Fin n) :
    vertexValue (negInputGates n) x (n + i) = !x i := by
  have hi : (i : ℕ) < (negInputGates n).length := by simp
  have key := runWith_getD_gate DAGGate.eval (negInputGates n) (List.ofFn x) hi false
  rw [List.length_ofFn] at key
  rw [vertexValue, key]
  simp only [negInputGates, List.getElem_map, List.getElem_range, DAGGate.eval, List.all_cons,
    List.all_nil, Bool.and_true]
  rw [runWith_getD_of_lt _ _ _ (by simp)]
  simp

/-- The vertex of the literal `xᵢ` (if `b`) or `¬xᵢ` (if not `b`). -/
def litVertex (n : ℕ) (i : Fin n) (b : Bool) : ℕ := if b then i else n + i

/-- Literal vertices lie among the inputs and the negation gates. -/
theorem litVertex_lt (i : Fin n) (b : Bool) : litVertex n i b < n + n := by
  unfold litVertex; split_ifs <;> omega

/-- After the negation gates, the literal vertex of `(i, b)` holds `xᵢ == b`. -/
theorem vertexValue_litVertex (x : Fin n → Bool) (i : Fin n) (b : Bool) :
    vertexValue (negInputGates n) x (litVertex n i b) = (x i == b) := by
  unfold litVertex
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, vertexValue_negInputGates]; cases x i <;> rfl
  · simp only [↓reduceIte, vertexValue_input]; cases x i <;> rfl

/-- The leaves of the minterm of `v`: the literal of each variable agreeing with `v`. -/
def mintermLeaves (v : Fin n → Bool) : List ℕ :=
  (List.finRange n).map fun i => litVertex n i (v i)

/-- The minterm gate of `v`, read after the negation gates, is true exactly at `v`. -/
theorem mintermLeaves_eval (v x : Fin n → Bool) :
    (⟨.and, mintermLeaves v⟩ : DAGGate).eval
      (runWith DAGGate.eval (negInputGates n) (List.ofFn x)) = decide (x = v) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [DAGGate.eval, mintermLeaves, List.all_map, List.all_eq_true, List.mem_finRange,
    true_implies, Function.comp_apply]
  change (∀ i, vertexValue (negInputGates n) x (litVertex n i (v i)) = true) ↔ _
  simp only [vertexValue_litVertex, beq_iff_eq]
  exact ⟨funext, fun h i => congrFun h i⟩

/-- The satisfying assignments of `f`, in some order. -/
noncomputable def satList (f : (Fin n → Bool) → Bool) : List (Fin n → Bool) :=
  (Finset.univ.filter fun v => f v = true).toList

/-- The gates of the DNF circuit: the negation gates, a balanced `∧`-tree per satisfying
assignment, and a balanced `∨`-tree over their roots. -/
noncomputable def dnfGates (f : (Fin n → Bool) → Bool) : List DAGGate × ℕ :=
  let r := emitTrees n .and ((satList f).map mintermLeaves) (negInputGates n)
  emitTree n .or r.2 r.1

private theorem minterms_spec (f : (Fin n → Bool) → Bool) :
    TreesSpec n .and ((satList f).map mintermLeaves) (negInputGates n)
      (emitTrees n .and ((satList f).map mintermLeaves) (negInputGates n)) := by
  refine emitTrees_spec .and (by decide) _ _ negInputGates_acyclic ?_
  intro vs hvs v hv
  obtain ⟨u, -, rfl⟩ := List.mem_map.mp hvs
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hv
  simpa using litVertex_lt i (u i)

private theorem dnf_spec (f : (Fin n → Bool) → Bool) :
    TreeSpec n .or (emitTrees n .and ((satList f).map mintermLeaves) (negInputGates n)).2
      (emitTrees n .and ((satList f).map mintermLeaves) (negInputGates n)).1 (dnfGates f) :=
  emitTree_spec .or (by decide) _ _ (minterms_spec f).acyclic (minterms_spec f).vertex_lt

/-- The DNF circuit of `f` in the book's model: `n` shared `¬` gates, one balanced
fan-in-two `∧`-tree per satisfying assignment, and a balanced fan-in-two `∨`-tree on top.
[AB09, Claim 2.13] -/
noncomputable def dnfDAG (f : (Fin n → Bool) → Bool) : DAGCircuit n where
  gates := (dnfGates f).1
  output := (dnfGates f).2
  args_lt := (dnf_spec f).acyclic
  output_lt := (dnf_spec f).vertex_lt

/-- `dnfDAG f` computes `f`. -/
theorem dnfDAG_eval (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    (dnfDAG f).eval x = f x := by
  have h := (dnf_spec f).value x
  change vertexValue (dnfGates f).1 x (dnfGates f).2 = f x
  rw [h]
  set r := emitTrees n .and ((satList f).map mintermLeaves) (negInputGates n)
  have hv := (minterms_spec f).value x
  simp only [DAGGate.eval]
  change r.2.any (vertexValue r.1 x) = f x
  have hany : r.2.any (vertexValue r.1 x) = (r.2.map (vertexValue r.1 x)).any id := by
    simp [List.any_map]
  have hfun : ((fun vs => (⟨.and, vs⟩ : DAGGate).eval
      (runWith DAGGate.eval (negInputGates n) (List.ofFn x))) ∘ mintermLeaves) =
      fun v => decide (x = v) := funext fun v => mintermLeaves_eval v x
  rw [hany, hv, List.map_map, hfun, Bool.eq_iff_iff]
  simp [satList]

/-- `dnfDAG f` has fan-in two. -/
theorem dnfDAG_isFaninTwo (f : (Fin n → Bool) → Bool) : (dnfDAG f).IsFaninTwo := by
  have h1 := minterms_spec f
  have h2 := dnf_spec f
  obtain ⟨e1, he1⟩ := h1.extends_gates
  obtain ⟨e2, he2⟩ := h2.extends_gates
  have key : ∀ g ∈ (dnfGates f).1, g.args.Nodup ∧ (g.kind = .not → g.args.length = 1) ∧
      g.args.length ≤ 2 := by
    intro g hg
    rw [he2, he1, List.mem_append, List.mem_append] at hg
    rcases hg with (hg | hg) | hg
    · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hg
      simp
    · obtain ⟨hk, hnd, hl⟩ := h1.new_gates g (by rw [he1, List.drop_left]; exact hg)
      exact ⟨hnd, fun h => absurd (hk ▸ h) (by decide), hl⟩
    · obtain ⟨hk, hnd, hl⟩ := h2.new_gates g (by rw [he2, List.drop_left]; exact hg)
      exact ⟨hnd, fun h => absurd (hk ▸ h) (by decide), hl⟩
  exact ⟨fun g hg => ⟨(key g hg).1, (key g hg).2.1⟩, fun g hg => (key g hg).2.2⟩

/-- `s` minterm trees of cost `treeCost n` and one `∨`-tree over `s ≤ 2ⁿ` roots cost at
most `n 2ⁿ + 1` gates. -/
private theorem dnf_cost_le {s : ℕ} (hs : s ≤ 2 ^ n) :
    s * treeCost n + treeCost s ≤ n * 2 ^ n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [pow_zero] at hs
    rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl <;> simp [treeCost]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases Nat.eq_zero_or_pos s with rfl | hs0
  · simp [treeCost]
  have h1 : treeCost (m + 1) = m := by simp [treeCost]
  have h2 : treeCost s = s - 1 := by simp [treeCost]; omega
  have : s * m ≤ 2 ^ (m + 1) * m := Nat.mul_le_mul_right m hs
  have : (m + 1) * 2 ^ (m + 1) = 2 ^ (m + 1) * m + 2 ^ (m + 1) := by ring
  rw [h1, h2]
  omega

/-- `dnfDAG f` has at most `n 2ⁿ + 2n + 1` vertices: `n` inputs, `n` negation gates,
`n - 1` gates per satisfying assignment and fewer than `2ⁿ` gates on top.

**Proof sketch.** The DAG consists of the `n` inputs, the `n` input negations, one
`∧`-tree per satisfying assignment, and one `∨`-tree over their roots. Each minterm tree
has `n` leaves and so costs `treeCost n` gates, giving a total of
`(#satisfying assignments) · treeCost n` for the minterm layer. There are at most `2ⁿ`
satisfying assignments, so the cost bound for `s ≤ 2ⁿ` minterm trees plus one `∨`-tree
over `s` roots (at most `n 2ⁿ + 1`) together with the `2n` inputs and negations yields
the claim by linear arithmetic. -/
theorem dnfDAG_size_le (f : (Fin n → Bool) → Bool) :
    (dnfDAG f).size ≤ n * 2 ^ n + 2 * n + 1 := by
  have h1 := minterms_spec f
  have h2 := dnf_spec f
  have hl1 := h1.length_le
  have hl2 := h2.length_le
  have hsum : (((satList f).map mintermLeaves).map fun vs => treeCost vs.length).sum =
      (satList f).length * treeCost n := by
    rw [List.map_map]
    have : ((fun vs : List ℕ => treeCost vs.length) ∘ mintermLeaves) =
        fun _ : Fin n → Bool => treeCost n := by
      funext v; simp [mintermLeaves]
    rw [this, List.map_const', List.sum_replicate, smul_eq_mul]
  have hs : (satList f).length ≤ 2 ^ n := by
    rw [satList, Finset.length_toList]
    exact (Finset.card_filter_le _ _).trans (by simp)
  rw [hsum, length_negInputGates] at hl1
  rw [h1.length_eq, List.length_map] at hl2
  have := dnf_cost_le hs
  change n + (dnfGates f).1.length ≤ _
  omega

/-- Every Boolean function on `n` bits is computed by a fan-in-two circuit of the book's
model with at most `n 2ⁿ + 2n + 1` vertices.  [AB09, Claim 2.13], as restated on
[AB09, p. 108] ("every function `f` from `{0,1}ⁿ` to `{0,1}` can be computed by a Boolean
circuit of size `n2ⁿ`").

The circuit is the DNF over `f`'s satisfying assignments (the book uses the dual CNF over
the falsifying ones; the counts agree).  The `2n + 1` beyond the book's `n2ⁿ` is the `n`
input vertices (counted by [AB09, Def 6.1]'s size), the `n` shared `¬` gates, and one
gate for the degenerate cases. -/
theorem exists_dagCircuit_faninTwo_size_le (f : (Fin n → Bool) → Bool) :
    ∃ C : DAGCircuit n, C.IsFaninTwo ∧ (∀ x, C.eval x = f x) ∧
      C.size ≤ n * 2 ^ n + 2 * n + 1 :=
  ⟨dnfDAG f, dnfDAG_isFaninTwo f, dnfDAG_eval f, dnfDAG_size_le f⟩

end BoolCircuit
