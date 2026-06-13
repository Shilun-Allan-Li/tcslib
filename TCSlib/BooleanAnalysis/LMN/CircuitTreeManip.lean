import TCSlib.BooleanAnalysis.LMN.CircuitCompression
import TCSlib.BooleanAnalysis.LMN.CompressionStep
import TCSlib.BooleanAnalysis.LMN.CircuitReindex
import TCSlib.BooleanAnalysis.LMN.GateMerge
import Mathlib

/-!
# Circuit Tree Manipulation for LMN Layer Reduction

This file provides formal infrastructure for navigating and transforming the
`Circuit` tree type, enabling one-level absorption of the top circuit `c_top`
into the Layer2Data gates.

## Main results

- `dnfToDualCNF`: Convert a DNF to its De Morgan dual CNF (negating literals).
- `Circuit.exists_node_of_depth_ge_one`: Depth ≥ 1 implies a node.
- `or_of_lit_children_dnf` / `and_of_lit_children_cnf`: Compression for all-literal nodes.
- `absorbOneLevel_depth1`: Absorb a depth-1 c_top into gates (depth 0 output).
- `absorbOneLevel_general`: Absorb children of depth-≥-2 c_top (depth ≤ 1 output).
- `absorbOneLevel`: Combined — reduce c_top depth by ≥ 1.
- `switched_gates_have_dnf_cnf`: After switching, gates have both DNF and CNF reps.
-/

open BoolCircuit SwitchingLemma2 SwitchingBernoulli LMN
open Classical in
attribute [local instance] Classical.propDecidable
noncomputable section

namespace LMN

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ## DNF to dual CNF conversion -/

/-- Convert a DNF to its De Morgan dual CNF by negating every literal.
    `¬(∨ᵢ (∧ⱼ lᵢⱼ)) = ∧ᵢ (∨ⱼ ¬lᵢⱼ)` -/
def dnfToDualCNF {n : ℕ} (φ : DNF n) : CNF n :=
  φ.map (fun term => term.map Literal.flipNeg)

lemma dnfToDualCNF_width {n : ℕ} (φ : DNF n) :
    (dnfToDualCNF φ).width = φ.width := by
  simp only [dnfToDualCNF, CNF.width, DNF.width, Term.width,
    List.map_map, Function.comp_def, List.length_map]; congr 1

lemma dnfToDualCNF_eval {n : ℕ} (φ : DNF n) (x : Fin n → Bool) :
    CNF.eval (dnfToDualCNF φ) x = !(DNF.eval φ x) := by
  simp only [dnfToDualCNF, CNF.eval, DNF.eval]
  induction φ with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.all_cons, List.any_cons]
    rw [ih, Bool.not_or]; congr 1
    simp only [Term.eval, CNF.evalClause]
    induction hd with
    | nil => simp
    | cons l tl' ih' =>
      simp only [List.map_cons, List.all_cons, List.any_cons, Literal.flipNeg_eval]
      rw [ih', Bool.not_and]

/-! ## Circuit structural helpers -/

/-- A circuit of depth ≥ 1 must be a node. -/
lemma Circuit.exists_node_of_depth_ge_one {m : ℕ} (c : Circuit m) (h : 1 ≤ c.depth) :
    ∃ isAnd cs, c = Circuit.node isAnd cs := by
  cases c with
  | lit l => simp [Circuit.depth] at h
  | node isAnd cs => exact ⟨isAnd, cs, rfl⟩

/-- In a depth-1 node, all children have depth 0 (= are literals). -/
lemma Circuit.depth1_children_are_lits {m : ℕ} (isAnd : Bool) (cs : List (Circuit m))
    (h : (Circuit.node isAnd cs).depth ≤ 1) :
    ∀ c ∈ cs, c.depth = 0 := by
  intro c hc
  simp [Circuit.depth] at h
  have hmaxd : cs.foldr (fun c acc => max c.depth acc) 0 = 0 := by omega
  have : c.depth ≤ cs.foldr (fun c acc => max c.depth acc) 0 := by
    clear h hmaxd
    induction cs with
    | nil => simp at hc
    | cons hd tl ih =>
      simp only [List.foldr]
      rcases List.mem_cons.mp hc with rfl | hmem
      · exact le_max_left _ _
      · exact le_trans (ih hmem) (le_max_right _ _)
  omega

/-- A depth-0 circuit is a literal. -/
lemma Circuit.depth0_is_lit {m : ℕ} (c : Circuit m) (h : c.depth = 0) :
    ∃ lr : Lit m, c = Circuit.lit lr := by
  cases c with
  | lit l => exact ⟨l, rfl⟩
  | node _ _ => simp [Circuit.depth] at h

/-- In a depth-1 node, all children are literals. -/
lemma Circuit.depth1_all_lits {m : ℕ} (isAnd : Bool) (cs : List (Circuit m))
    (h : (Circuit.node isAnd cs).depth ≤ 1) :
    ∀ c ∈ cs, ∃ lr : Lit m, c = Circuit.lit lr := by
  intro c hc
  exact Circuit.depth0_is_lit c (Circuit.depth1_children_are_lits isAnd cs h c hc)

/-! ## Child function -/

/-- The function computed by a subcircuit when gates are substituted. -/
def childFunction {m : ℕ} (c_sub : Circuit m) (gates : Fin m → (Fin n → Bool) → Bool) :
    (Fin n → Bool) → Bool :=
  fun x => c_sub.eval (fun i => gates i x)

/-! ## Switched gates give DNF and CNF -/

/-- After switching (dtDepth ≤ l for all gates), each gate has both
    a clean width-l DNF and a width-l CNF representation. -/
lemma switched_gates_have_dnf_cnf
    (m : ℕ) (gates : Fin m → DNF n) (ρ : Restriction n) (l : ℕ)
    (h_switch : ∀ i, dtDepth (restrictFn (gates i).eval ρ) ≤ l) :
    (∀ i, ∃ φ : DNF n, φ.width ≤ l ∧
      (∀ x, φ.eval x = restrictFn (gates i).eval ρ x) ∧
      (∀ t ∈ φ, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂) ∧
      (∀ t ∈ φ, t.Nodup)) ∧
    (∀ i, ∃ ψ : CNF n, ψ.width ≤ l ∧
      ∀ x, CNF.eval ψ x = restrictFn (gates i).eval ρ x) := by
  exact ⟨fun i => by
    obtain ⟨⟨φ₀, hw₀, he₀⟩, _⟩ := dtDepth_le_implies_small_dnf_cnf _ l (h_switch i)
    exact ⟨cleanDNF φ₀, le_trans (cleanDNF_width_le φ₀) hw₀,
      fun x => by rw [cleanDNF_eval]; exact he₀ x,
      cleanDNF_var_inj φ₀, cleanDNF_nodup φ₀⟩,
   fun i => by
    obtain ⟨_, ⟨ψ₀, hw₀, he₀⟩⟩ := dtDepth_le_implies_small_dnf_cnf _ l (h_switch i)
    exact ⟨ψ₀, hw₀, he₀⟩⟩

/-! ## OR-of-literal-children → width-l DNF -/

/-
An OR node with all-literal children, where each gate has width-l DNF
    and CNF, evaluates as a function that has a width-l DNF.
-/
lemma or_of_lit_children_dnf
    {m : ℕ} (cs : List (Circuit m))
    (gates : Fin m → (Fin n → Bool) → Bool) (l : ℕ)
    (h_all_lits : ∀ c ∈ cs, ∃ lr : Lit m, c = Circuit.lit lr)
    (hDNF : ∀ i, ∃ φ : DNF n, φ.width ≤ l ∧ ∀ x, φ.eval x = gates i x)
    (hCNF : ∀ i, ∃ ψ : CNF n, ψ.width ≤ l ∧ ∀ x, CNF.eval ψ x = gates i x) :
    ∃ φ : DNF n, φ.width ≤ l ∧
      ∀ x, φ.eval x = (Circuit.node false cs).eval (fun i => gates i x) := by
  -- Let's express the children's functions in terms of their DNF and CNF representations.
  have h_child_functions : ∀ c ∈ cs, ∃ f : (Fin n → Bool) → Bool, (∃ φ : DNF n, φ.width ≤ l ∧ ∀ x, φ.eval x = f x) ∧ ∀ x, f x = c.eval (fun i => gates i x) := by
    intro c hc; obtain ⟨ lr, rfl ⟩ := h_all_lits c hc; simp +decide [ Circuit.eval ] ;
    split_ifs <;> [ exact ⟨ _, hDNF _, fun x => rfl ⟩ ; exact ⟨ _, by simpa [ cnfToDualDNF_eval ] using Exists.elim ( hCNF lr.idx ) fun ψ hψ => ⟨ cnfToDualDNF ψ, by simpa [ cnfToDualDNF_width ] using hψ.1, fun x => by simp +decide [ hψ.2, cnfToDualDNF_eval ] ⟩, fun x => rfl ⟩ ];
  choose! f hf₁ hf₂ using h_child_functions;
  -- By definition of `Circuit.eval`, we know that `Circuit.node false cs` evaluates to the OR of the children's functions.
  have h_eval_or : ∀ x, (Circuit.node false cs).eval (fun i => gates i x) = (cs.any (fun c => f c x)) := by
    intro x
    simp [Circuit.eval, hf₂];
    induction cs <;> aesop;
  obtain ⟨ φ, hφ₁, hφ₂ ⟩ := compression_or_of_dnfs ( cs.map f ) l ( by aesop );
  use φ; aesop;

/-
An AND node with all-literal children, where each gate has width-l DNF
    and CNF, evaluates as a function that has a width-l CNF.
-/
lemma and_of_lit_children_cnf
    {m : ℕ} (cs : List (Circuit m))
    (gates : Fin m → (Fin n → Bool) → Bool) (l : ℕ)
    (h_all_lits : ∀ c ∈ cs, ∃ lr : Lit m, c = Circuit.lit lr)
    (hDNF : ∀ i, ∃ φ : DNF n, φ.width ≤ l ∧ ∀ x, φ.eval x = gates i x)
    (hCNF : ∀ i, ∃ ψ : CNF n, ψ.width ≤ l ∧ ∀ x, CNF.eval ψ x = gates i x) :
    ∃ ψ : CNF n, ψ.width ≤ l ∧
      ∀ x, CNF.eval ψ x = (Circuit.node true cs).eval (fun i => gates i x) := by
  convert compression_and_of_cnfs _ l _;
  case convert_2 => exact cs.map fun c => fun x => c.eval ( fun i => gates i x );
  · -- By definition of `Circuit.eval`, the evaluation of an AND node is the conjunction of the evaluations of its children.
    simp [Circuit.eval];
    induction cs <;> aesop;
  · intro f hf; obtain ⟨ c, hc, rfl ⟩ := List.mem_map.mp hf; obtain ⟨ lr, rfl ⟩ := h_all_lits c hc; simp +decide [ Circuit.eval ] ;
    split_ifs <;> [ exact hCNF _; exact ⟨ dnfToDualCNF ( Classical.choose ( hDNF _ ) ), by simpa using dnfToDualCNF_width ( Classical.choose ( hDNF _ ) ) ▸ Classical.choose_spec ( hDNF _ ) |>.1, fun x => by simp +decide [ dnfToDualCNF_eval, Classical.choose_spec ( hDNF _ ) |>.2 ] ⟩ ];
    obtain ⟨ φ, hφ₁, hφ₂ ⟩ := hDNF lr.idx; use dnfToDualCNF φ; simp_all +decide [ dnfToDualCNF_width, dnfToDualCNF_eval ] ;

/-! ## Depth-1 absorption -/

/-
**Absorb a depth-1 c_top into gates.**
    When c_top has depth exactly 1 (node with all-literal children),
    and all gate functions have width-l DNF and CNF representations,
    the composed function can be expressed as a single-gate Layer2Data
    with c_top' of depth 0.
-/
lemma absorbOneLevel_depth1
    (data : Layer2Data n) (c_top : Circuit data.numGates)
    (l : ℕ) (hl : 0 < l)
    (h_depth_le : c_top.depth ≤ 1) (h_depth_ge : 1 ≤ c_top.depth)
    (hDNF_fn : ∀ i, ∃ φ : DNF n, φ.width ≤ l ∧
      (∀ x, φ.eval x = (data.gates i).eval x) ∧
      (∀ t ∈ φ, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂) ∧
      (∀ t ∈ φ, t.Nodup))
    (hCNF_fn : ∀ i, ∃ ψ : CNF n, ψ.width ≤ l ∧
      ∀ x, CNF.eval ψ x = (data.gates i).eval x) :
    ∃ (data' : Layer2Data n) (c_top' : Circuit data'.numGates),
      c_top'.depth = 0 ∧ data'.width ≤ l ∧
      (∀ x, c_top.eval (fun i => (data.gates i).eval x) =
            c_top'.eval (fun j => (data'.gates j).eval x)) := by
  -- Extract the node using Circuit.exists_node_of_depth_ge_one.
  obtain ⟨isAnd, cs, hc⟩ : ∃ isAnd cs, c_top = Circuit.node isAnd cs := Circuit.exists_node_of_depth_ge_one c_top h_depth_ge;
  by_cases h : isAnd <;> simp_all +decide only [Circuit.node];
  · obtain ⟨ ψ, hψ₁, hψ₂ ⟩ := and_of_lit_children_cnf cs ( fun i => ( data.gates i ).eval ) l ( Circuit.depth1_all_lits true cs h_depth_le ) ( fun i => by obtain ⟨ φ, hφ₁, hφ₂, hφ₃, hφ₄ ⟩ := hDNF_fn i; exact ⟨ φ, hφ₁, hφ₂ ⟩ ) ( fun i => by obtain ⟨ ψ, hψ₁, hψ₂ ⟩ := hCNF_fn i; exact ⟨ ψ, hψ₁, hψ₂ ⟩ );
    -- Use the CNF ψ to construct the new Layer2Data and Circuit.
    use ⟨1, fun _ => cleanDNF (cnfToDualDNF ψ), l, by
      exact fun _ => le_trans ( cleanDNF_width_le _ ) ( cnfToDualDNF_width _ ▸ hψ₁ ), by
      grind, by
      exact fun i t ht l₁ hl₁ l₂ hl₂ h => cleanDNF_var_inj _ _ ht _ hl₁ _ hl₂ h, by
      exact fun _ _ ht => cleanDNF_nodup _ _ ht⟩, Circuit.lit ⟨0, false⟩
    generalize_proofs at *;
    simp +decide [ Circuit.eval, hψ₂ ];
    simp +decide [ Circuit.depth, cleanDNF_eval ];
    simp +decide [ Circuit.eval, cnfToDualDNF_eval ] at hψ₂ ⊢;
    exact fun x => hψ₂ x ▸ rfl;
  · obtain ⟨φ, hφ⟩ : ∃ φ : DNF n, φ.width ≤ l ∧ ∀ x, φ.eval x = (Circuit.node false cs).eval (fun i => (data.gates i).eval x) := by
      apply or_of_lit_children_dnf cs (fun i => (data.gates i).eval) l (Circuit.depth1_all_lits false cs h_depth_le) (fun i => by
        exact Exists.imp ( fun φ => by tauto ) ( hDNF_fn i )) (fun i => by
        exact hCNF_fn i);
    refine' ⟨ ⟨ 1, fun _ => cleanDNF φ, l, _, _, _, _ ⟩, Circuit.lit ⟨ 0, true ⟩, _, _, _ ⟩ <;> norm_num [ hφ ];
    all_goals norm_num [ Circuit.depth, Circuit.eval ] at *;
    · exact le_trans ( cleanDNF_width_le φ ) hφ.1;
    · linarith;
    · exact fun t ht l₁ hl₁ l₂ hl₂ hvar => cleanDNF_var_inj φ t ht l₁ hl₁ l₂ hl₂ hvar;
    · exact fun t ht => cleanDNF_nodup φ t ht;
    · exact fun x => hφ.2 x ▸ cleanDNF_eval φ x ▸ rfl

/-! ## General depth ≥ 2 absorption -/

/-
For a depth-≤-1 child of c_top (with access to width-l DNF/CNF gate reps),
    the child function has a width-l **signed** DNF representation.
    Returns (φ, sign) where the signed evaluation matches the child function:
    `if sign then φ.eval else !φ.eval = c_j.eval(gates)`
-/
lemma child_depth_le1_has_signed_dnf
    {m : ℕ} (c_j : Circuit m) (gates : Fin m → (Fin n → Bool) → Bool) (l : ℕ)
    (hd : c_j.depth ≤ 1)
    (hDNF : ∀ i, ∃ φ : DNF n, φ.width ≤ l ∧ ∀ x, φ.eval x = gates i x)
    (hCNF : ∀ i, ∃ ψ : CNF n, ψ.width ≤ l ∧ ∀ x, CNF.eval ψ x = gates i x) :
    ∃ (φ : DNF n) (sign : Bool), φ.width ≤ l ∧
      (∀ x, (if sign then φ.eval x else !(φ.eval x)) = c_j.eval (fun i => gates i x)) ∧
      (∀ t ∈ φ, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂) ∧
      (∀ t ∈ φ, t.Nodup) := by
  by_cases h : c_j.depth = 0;
  · obtain ⟨lr, hr⟩ : ∃ lr : Lit m, c_j = Circuit.lit lr := by
      exact?;
    by_cases h : lr.sign <;> simp_all +decide [ Circuit.eval ];
    · obtain ⟨ φ, hφ₁, hφ₂ ⟩ := hDNF lr.idx;
      use cleanDNF φ;
      exact ⟨ le_trans ( cleanDNF_width_le φ ) hφ₁, Or.inr fun x => by rw [ cleanDNF_eval, hφ₂ ], cleanDNF_var_inj φ, cleanDNF_nodup φ ⟩;
    · obtain ⟨ φ, hφ₁, hφ₂ ⟩ := hDNF lr.idx;
      use cleanDNF φ;
      exact ⟨ le_trans ( cleanDNF_width_le φ ) hφ₁, Or.inl fun x => by rw [ cleanDNF_eval, hφ₂ ], cleanDNF_var_inj φ, cleanDNF_nodup φ ⟩;
  · obtain ⟨isAnd, cs, hc⟩ : ∃ isAnd cs, c_j = Circuit.node isAnd cs := by
      exact LMN.Circuit.exists_node_of_depth_ge_one _ ( Nat.pos_of_ne_zero h );
    by_cases h : isAnd <;> simp_all +decide [ Circuit.depth ];
    · obtain ⟨ψ, hψ⟩ : ∃ ψ : CNF n, ψ.width ≤ l ∧ ∀ x, CNF.eval ψ x = (Circuit.node true cs).eval (fun i => gates i x) := by
        apply and_of_lit_children_cnf cs gates l (Circuit.depth1_all_lits true cs (by
        unfold Circuit.depth; aesop;)) hDNF hCNF;
      refine' ⟨ cleanDNF ( cnfToDualDNF ψ ), _, _, _, _ ⟩;
      · exact le_trans ( cleanDNF_width_le _ ) ( by simpa [ cnfToDualDNF_width ] using hψ.1 );
      · exact Or.inl fun x => by rw [ ← hψ.2 x, cleanDNF_eval, cnfToDualDNF_eval ] ;
      · exact fun t ht l₁ hl₁ l₂ hl₂ h => cleanDNF_var_inj _ _ ht _ hl₁ _ hl₂ h;
      · exact fun t ht => cleanDNF_nodup _ _ ht;
    · -- By or_of_lit_children_dnf, there exists a width-l DNF φ such that φ.eval = c_j.eval(gates).
      obtain ⟨φ, hφ⟩ := or_of_lit_children_dnf cs gates l (by
      apply Circuit.depth1_all_lits;
      rw [ Circuit.depth ];
      · linarith;
      · exact isAnd) hDNF hCNF;
      use cleanDNF φ;
      exact ⟨ le_trans ( cleanDNF_width_le φ ) hφ.1, Or.inr fun x => by rw [ cleanDNF_eval, hφ.2 ], cleanDNF_var_inj φ, cleanDNF_nodup φ ⟩

/-! ## General depth reduction -/

/-
Helper: extract signed DNFs for each element of a list of depth-≤-1 circuits.
-/
lemma list_child_signed_dnfs
    {m : ℕ} (cs : List (Circuit m)) (gates : Fin m → (Fin n → Bool) → Bool)
    (l : ℕ)
    (h_depth : ∀ c ∈ cs, c.depth ≤ 1)
    (hDNF : ∀ i, ∃ φ : DNF n, φ.width ≤ l ∧ ∀ x, φ.eval x = gates i x)
    (hCNF : ∀ i, ∃ ψ : CNF n, ψ.width ≤ l ∧ ∀ x, CNF.eval ψ x = gates i x) :
    ∃ (φs : Fin cs.length → DNF n) (signs : Fin cs.length → Bool),
      (∀ j, (φs j).width ≤ l) ∧
      (∀ j, ∀ t ∈ φs j, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂) ∧
      (∀ j, ∀ t ∈ φs j, t.Nodup) ∧
      (∀ j x, (if signs j then (φs j).eval x else !((φs j).eval x)) =
        (cs.get j).eval (fun i => gates i x)) := by
  have h_choose : ∀ j : Fin cs.length, ∃ (φ : DNF n) (sign : Bool), φ.width ≤ l ∧ (∀ x, (if sign then φ.eval x else !(φ.eval x)) = (cs.get j).eval (fun i => gates i x)) ∧ (∀ t ∈ φ, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂) ∧ (∀ t ∈ φ, t.Nodup) := by
    intro j;
    apply_rules [ child_depth_le1_has_signed_dnf ];
    grind;
  choose φ sign hφ hsign using h_choose;
  exact ⟨ φ, sign, hφ, fun j => hsign j |>.2.1, fun j => hsign j |>.2.2, fun j x => hsign j |>.1 x ⟩

/-
Helper: build a circuit of literals from signed DNFs and prove depth/eval.
-/
lemma build_literal_circuit (isAnd : Bool) (k : ℕ)
    (signs : Fin k → Bool) :
    ∃ c' : Circuit k, c'.depth ≤ 1 ∧
      ∀ (g : Fin k → Bool),
        c'.eval g = (Circuit.node isAnd
          ((List.finRange k).map (fun j => Circuit.lit ⟨j, signs j⟩))).eval g := by
  exact ⟨Circuit.node isAnd ((List.finRange k).map (fun j => Circuit.lit ⟨j, signs j⟩)),
    by
      induction' k with k ih;
      · cases isAnd <;> simp +decide [ Circuit.depth ];
      · induction' ( List.finRange ( k + 1 ) ) with j hj <;> simp_all +arith +decide [ Circuit.depth ], fun g => rfl⟩

/-- Depth reduction for depth-1 circuits: collapse to a single gate. -/
lemma exists_circuit_depth_reduction_depth1
    {m : ℕ} (c : Circuit m) (gates : Fin m → (Fin n → Bool) → Bool)
    (l : ℕ) (h_depth : c.depth = 1)
    (hDNF : ∀ i, ∃ φ : DNF n, φ.width ≤ l ∧ ∀ x, φ.eval x = gates i x)
    (hCNF : ∀ i, ∃ ψ : CNF n, ψ.width ≤ l ∧ ∀ x, CNF.eval ψ x = gates i x) :
    ∃ (φ : DNF n) (sign : Bool),
      φ.width ≤ l ∧
      (∀ t ∈ φ, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂) ∧
      (∀ t ∈ φ, t.Nodup) ∧
      (∀ x, (if sign then φ.eval x else !(φ.eval x)) = c.eval (fun i => gates i x)) := by
  obtain ⟨φ, sign, hw, he, hvi, hnd⟩ := child_depth_le1_has_signed_dnf c gates l (by omega) hDNF hCNF
  exact ⟨φ, sign, hw, hvi, hnd, he⟩

/-
Depth reduction for depth-2 circuits: collapse children to gates.
-/
lemma exists_circuit_depth_reduction_depth2
    {m : ℕ} (c : Circuit m) (gates : Fin m → (Fin n → Bool) → Bool)
    (l : ℕ) (h_depth : c.depth = 2)
    (hDNF : ∀ i, ∃ φ : DNF n, φ.width ≤ l ∧ ∀ x, φ.eval x = gates i x)
    (hCNF : ∀ i, ∃ ψ : CNF n, ψ.width ≤ l ∧ ∀ x, CNF.eval ψ x = gates i x) :
    ∃ (m' : ℕ) (gates' : Fin m' → DNF n) (c' : Circuit m'),
      c'.depth ≤ 1 ∧
      (∀ j, (gates' j).width ≤ l) ∧
      (∀ j, ∀ t ∈ gates' j, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂) ∧
      (∀ j, ∀ t ∈ gates' j, t.Nodup) ∧
      (∀ x, c.eval (fun i => gates i x) = c'.eval (fun j => (gates' j).eval x)) := by
  obtain ⟨isAnd, cs, hc⟩ : ∃ isAnd cs, c = Circuit.node isAnd cs := Circuit.exists_node_of_depth_ge_one c (by linarith);
  obtain ⟨φs, signs, h_width, h_var_inj, h_nodup, h_eval⟩ : ∃ (φs : Fin cs.length → DNF n) (signs : Fin cs.length → Bool),
    (∀ j, (φs j).width ≤ l) ∧
    (∀ j, ∀ t ∈ φs j, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂) ∧
    (∀ j, ∀ t ∈ φs j, t.Nodup) ∧
    (∀ j x, (if signs j then (φs j).eval x else !((φs j).eval x)) = (cs.get j).eval (fun i => gates i x)) := by
      apply_rules [ list_child_signed_dnfs ];
      intro c hc; have := h_depth; simp_all +decide [ Circuit.depth ] ;
      have h_max_depth : ∀ {l : List (Circuit m)}, c ∈ l → List.foldr (fun c acc => max c.depth acc) 0 l ≥ c.depth := by
        intros l hl; induction l <;> aesop;
      linarith [ h_max_depth hc ];
  obtain ⟨c', hc', hc'_eval⟩ := build_literal_circuit isAnd cs.length signs;
  refine' ⟨ cs.length, φs, c', hc', h_width, h_var_inj, h_nodup, _ ⟩;
  intro x; rw [ hc, hc'_eval ] ;
  cases isAnd <;> simp +decide [ *, Circuit.eval ];
  · have h_foldr_eq : ∀ (l : List (Fin cs.length)), List.foldr (fun j acc => (cs.get j).eval (fun i => gates i x) || acc) false l = List.foldr (fun j acc => (if signs j then (φs j).eval x else !((φs j).eval x)) || acc) false l := by
      intro l; induction l <;> simp +decide [ * ] ;
    convert h_foldr_eq ( List.finRange cs.length ) using 1;
    · refine' List.recOn cs _ _ <;> simp +decide [ List.finRange_succ ];
      intro head tail ih; rw [ List.foldr_map ] ; simp +decide [ List.finRange_succ ] ;
      rw [ ih ];
    · induction ( List.finRange cs.length ) <;> simp +decide [ * ];
      simp +decide [ Circuit.eval, h_eval ];
  · have h_foldr_eq : ∀ (l : List (Fin cs.length)), List.foldr (fun c acc => (c.eval (fun i => gates i x)) && acc) true (List.map (fun j => cs.get j) l) = List.foldr (fun c acc => (c.eval (fun j => (φs j).eval x)) && acc) true (List.map (fun j => Circuit.lit ⟨j, signs j⟩) l) := by
      intro l; induction l <;> simp +decide [ * ] ;
      rename_i j l ih; specialize h_eval j x; cases h : signs j <;> simp_all +decide [ Circuit.eval ] ;
    convert h_foldr_eq ( List.finRange cs.length ) using 1;
    refine' congr_arg _ ( List.ext_get _ _ ) <;> simp +decide

/-
Helper: merge a list of child reduction results.
    Given that each child cⱼ of a circuit node has been individually
    reduced to (m_j, gates_j, c_j'), merge all gate sets into a single
    gate set indexed by `Fin M` and produce re-indexed circuits.
-/
lemma reduce_children
    {m : ℕ} (cs : List (Circuit m)) (gates : Fin m → (Fin n → Bool) → Bool)
    (l : ℕ) (bound : Fin cs.length → ℕ)
    (h_results : ∀ j : Fin cs.length,
      ∃ (m_j : ℕ) (g_j : Fin m_j → DNF n) (c_j : Circuit m_j),
        c_j.depth ≤ bound j ∧
        (∀ k, (g_j k).width ≤ l) ∧
        (∀ k, ∀ t ∈ g_j k, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂) ∧
        (∀ k, ∀ t ∈ g_j k, t.Nodup) ∧
        (∀ x, (cs.get j).eval (fun i => gates i x) =
              c_j.eval (fun k => (g_j k).eval x))) :
    ∃ (M : ℕ) (merged : Fin M → DNF n) (new_cs : Fin cs.length → Circuit M),
      (∀ k, (merged k).width ≤ l) ∧
      (∀ k, ∀ t ∈ merged k, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂) ∧
      (∀ k, ∀ t ∈ merged k, t.Nodup) ∧
      (∀ j, (new_cs j).depth ≤ bound j) ∧
      (∀ j x, (new_cs j).eval (fun k => (merged k).eval x) =
              (cs.get j).eval (fun i => gates i x)) := by
  choose m_j g_j c_j hc_j hg_j hg_j' hg_j'' hg_j''' using h_results;
  induction' cs with cs ih;
  · exact ⟨ 0, fun _ => ∅, fun _ => Fin.elim0 ‹_›, by simp +decide ⟩;
  · sorry -- TODO: cons case; type-synthesis failures in mergeGates/reidx refine'

/-
If each new child circuit evaluates the same as the corresponding original child,
    then the whole node evaluates the same.
-/
lemma node_eval_eq_of_finRange_map {m M : ℕ}
    (isAnd : Bool) (cs : List (Circuit m))
    (new_cs : Fin cs.length → Circuit M)
    (g : Fin m → Bool) (g' : Fin M → Bool)
    (heval : ∀ j, (new_cs j).eval g' = (cs.get j).eval g) :
    (Circuit.node isAnd cs).eval g =
    (Circuit.node isAnd ((List.finRange cs.length).map new_cs)).eval g' := by
  unfold Circuit.eval;
  cases isAnd <;> simp_all +decide [ List.finRange, List.map ];
  · have h_foldr_eq : ∀ (l : List (Fin cs.length)), List.foldr (fun c acc => c.eval g || acc) false (List.map (fun j => cs[j]) l) = List.foldr (fun c acc => c.eval g' || acc) false (List.map (fun j => new_cs j) l) := by
      intro l; induction l <;> aesop;
    convert h_foldr_eq ( List.finRange cs.length ) using 1;
    · refine' congr_arg _ ( List.ext_get _ _ ) <;> aesop;
    · exact congr_arg _ ( by rw [ List.ofFn_eq_map ] ; aesop );
  · induction cs <;> simp_all +decide [ List.ofFn_eq_map ];
    rename_i k hk ih; specialize ih ( fun i => new_cs i.succ ) ; aesop;

lemma exists_circuit_depth_reduction
    {m : ℕ} (c : Circuit m) (gates : Fin m → (Fin n → Bool) → Bool)
    (l : ℕ) (hl : 0 < l) (h_depth : 1 ≤ c.depth)
    (hDNF : ∀ i, ∃ φ : DNF n, φ.width ≤ l ∧
      (∀ x, φ.eval x = gates i x) ∧
      (∀ t ∈ φ, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂) ∧
      (∀ t ∈ φ, t.Nodup))
    (hCNF : ∀ i, ∃ ψ : CNF n, ψ.width ≤ l ∧ ∀ x, CNF.eval ψ x = gates i x) :
    ∃ (m' : ℕ) (gates' : Fin m' → DNF n) (c' : Circuit m'),
      c'.depth ≤ c.depth - 1 ∧
      (∀ j, (gates' j).width ≤ l) ∧
      (∀ j, ∀ t ∈ gates' j, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂) ∧
      (∀ j, ∀ t ∈ gates' j, t.Nodup) ∧
      (∀ x, c.eval (fun i => gates i x) = c'.eval (fun j => (gates' j).eval x)) := by
  -- Strong induction on c.depth
  suffices key : ∀ (D : ℕ) {m : ℕ} (c : Circuit m) (gates : Fin m → (Fin n → Bool) → Bool),
      c.depth = D → 1 ≤ D →
      (∀ i, ∃ φ : DNF n, φ.width ≤ l ∧ (∀ x, φ.eval x = gates i x) ∧
        (∀ t ∈ φ, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂) ∧ (∀ t ∈ φ, t.Nodup)) →
      (∀ i, ∃ ψ : CNF n, ψ.width ≤ l ∧ ∀ x, CNF.eval ψ x = gates i x) →
      ∃ (m' : ℕ) (gates' : Fin m' → DNF n) (c' : Circuit m'),
        c'.depth ≤ D - 1 ∧
        (∀ j, (gates' j).width ≤ l) ∧
        (∀ j, ∀ t ∈ gates' j, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂) ∧
        (∀ j, ∀ t ∈ gates' j, t.Nodup) ∧
        (∀ x, c.eval (fun i => gates i x) = c'.eval (fun j => (gates' j).eval x))
      from key c.depth c gates rfl h_depth hDNF hCNF
  intro D; induction D using Nat.strongRecOn with | _ D ih =>
  intro m c gates hcd hD1 hDNF hCNF
  -- Cases on D:
  by_cases h1 : D = 1
  · -- Depth 1: collapse entire circuit to a single gate
    subst h1
    obtain ⟨φ, sign, hw, hvi, hnd, he⟩ := exists_circuit_depth_reduction_depth1 c gates l hcd
      (fun i => by obtain ⟨φ, hw, he, _, _⟩ := hDNF i; exact ⟨φ, hw, he⟩) hCNF
    refine ⟨1, fun _ => φ, Circuit.lit ⟨0, sign⟩, by simp [Circuit.depth],
      fun _ => hw, fun _ => hvi, fun _ => hnd, fun x => ?_⟩
    simp only [Circuit.eval, Lit.eval]; exact (he x).symm
  · by_cases h2 : D = 2
    · -- Depth 2: collapse children to gates
      subst h2
      obtain ⟨m', gates', c', hd, hw, hvi, hnd, he⟩ := exists_circuit_depth_reduction_depth2
        c gates l hcd (fun i => by obtain ⟨φ, hw, he, _, _⟩ := hDNF i; exact ⟨φ, hw, he⟩) hCNF
      exact ⟨m', gates', c', by omega, hw, hvi, hnd, he⟩
    · -- Depth ≥ 3: process each child using IH, then merge gate sets
      have hD3 : 3 ≤ D := by omega
      obtain ⟨isAnd, cs, rfl⟩ := Circuit.exists_node_of_depth_ge_one c (by omega)
      -- Each child has depth < D
      have h_elem_le_foldr : ∀ (xs : List (Circuit m)) (j : Fin xs.length),
          (xs.get j).depth ≤ xs.foldr (fun c acc => max c.depth acc) 0 := by
        intro xs
        induction xs with
        | nil => intro j; exact absurd j.isLt (by simp)
        | cons hd tl ih =>
          intro ⟨j, hj⟩
          simp only [List.foldr]
          cases j with
          | zero => exact le_max_left _ _
          | succ k =>
            simp [List.length] at hj
            exact le_trans (ih ⟨k, by omega⟩) (le_max_right _ _)
      have h_child_depth : ∀ j : Fin cs.length,
          (cs.get j).depth ≤ D - 1 := by
        intro j; simp [Circuit.depth] at hcd
        have := h_elem_le_foldr cs j
        omega
      -- For each child, get a reduction result
      have h_child_results : ∀ j : Fin cs.length,
          ∃ (m_j : ℕ) (g_j : Fin m_j → DNF n) (c_j : Circuit m_j),
            c_j.depth ≤ (cs.get j).depth - 1 ∧
            (∀ k, (g_j k).width ≤ l) ∧
            (∀ k, ∀ t ∈ g_j k, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂) ∧
            (∀ k, ∀ t ∈ g_j k, t.Nodup) ∧
            (∀ x, (cs.get j).eval (fun i => gates i x) =
                  c_j.eval (fun k => (g_j k).eval x)) := by
        intro j
        by_cases hle : (cs.get j).depth ≤ 1
        · -- Depth ≤ 1: use child_depth_le1_has_signed_dnf
          obtain ⟨φ, sign, hw, he, hvi, hnd⟩ := child_depth_le1_has_signed_dnf (cs.get j)
            gates l hle (fun i => by obtain ⟨φ, hw, he, _, _⟩ := hDNF i; exact ⟨φ, hw, he⟩) hCNF
          exact ⟨1, fun _ => φ, Circuit.lit ⟨0, sign⟩, by simp [Circuit.depth],
            fun _ => hw, fun _ => hvi, fun _ => hnd,
            fun x => by simp [Circuit.eval, Lit.eval, he]⟩
        · -- Depth ≥ 2: apply IH
          push_neg at hle
          have hd_lt : (cs.get j).depth < D := by
            have := h_child_depth j; omega
          exact ih (cs.get j).depth hd_lt (cs.get j) gates rfl (by omega) hDNF hCNF
      -- Merge all child results using reduce_children with tight depth bound
      obtain ⟨M, merged, new_cs, hw, hvi, hnd, hdep, heval⟩ :=
        reduce_children cs gates l (fun j => (cs.get j).depth - 1) h_child_results
      -- Build the new top circuit
      -- Convert Fin-indexed children to a list
      let cs' := (List.finRange cs.length).map new_cs
      refine ⟨M, merged, Circuit.node isAnd cs', ?depth_bound, hw, hvi, hnd, ?eval_correct⟩
      case depth_bound =>
        -- Depth bound: 1 + max(cs'[j].depth) ≤ 1 + (D - 2) = D - 1
        simp only [Circuit.depth]
        suffices h_max : cs'.foldr (fun c acc => max c.depth acc) 0 ≤ D - 2 by omega
        -- Each element of cs' has depth ≤ D - 2
        have h_all_le : ∀ c' ∈ cs', c'.depth ≤ D - 2 := by
          intro c' hc'
          simp only [cs', List.mem_map, List.mem_finRange] at hc'
          obtain ⟨j, _, rfl⟩ := hc'
          have := hdep j
          have := h_child_depth j
          omega
        -- foldr max ≤ bound if all elements ≤ bound
        clear_value cs'
        induction cs' with
        | nil => simp
        | cons hd tl ih =>
          simp only [List.foldr]
          exact max_le (h_all_le hd List.mem_cons_self)
            (ih (fun c hc => h_all_le c (List.mem_cons_of_mem hd hc)))
      case eval_correct =>
        -- Evaluation correctness: Circuit.node isAnd cs' evals same as Circuit.node isAnd cs
        -- because cs' = finRange.map new_cs and each new_cs j evals = cs.get j
        intro x
        exact node_eval_eq_of_finRange_map isAnd cs new_cs
          (fun i => gates i x) (fun k => (merged k).eval x) (fun j => heval j x)

/-- Wrap `exists_circuit_depth_reduction` into the Layer2Data formulation. -/
lemma absorbOneLevel_general
    (data : Layer2Data n) (c_top : Circuit data.numGates)
    (l : ℕ) (hl : 0 < l)
    (h_depth : 2 ≤ c_top.depth)
    (hDNF_fn : ∀ i, ∃ φ : DNF n, φ.width ≤ l ∧
      (∀ x, φ.eval x = (data.gates i).eval x) ∧
      (∀ t ∈ φ, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂) ∧
      (∀ t ∈ φ, t.Nodup))
    (hCNF_fn : ∀ i, ∃ ψ : CNF n, ψ.width ≤ l ∧
      ∀ x, CNF.eval ψ x = (data.gates i).eval x) :
    ∃ (data' : Layer2Data n) (c_top' : Circuit data'.numGates),
      c_top'.depth ≤ c_top.depth - 1 ∧ data'.width ≤ l ∧
      (∀ x, c_top.eval (fun i => (data.gates i).eval x) =
            c_top'.eval (fun j => (data'.gates j).eval x)) := by
  obtain ⟨m', gates', c', hd, hw, hvi, hnd, he⟩ :=
    exists_circuit_depth_reduction c_top (fun i => (data.gates i).eval) l hl (by omega)
      hDNF_fn hCNF_fn
  exact ⟨⟨m', gates', l, hw, hl, hvi, hnd⟩, c', hd, le_refl l, he⟩

/-! ## Combined absorption -/

/-- **Absorb one level of c_top.**
    Given c_top with depth ≥ 1, and gate functions with width-l DNF/CNF
    representations, produce new Layer2Data + c_top' with reduced depth.

    - Depth 1 → depth 0
    - Depth ≥ 2 → depth ≤ 1 -/
lemma absorbOneLevel
    (data : Layer2Data n) (c_top : Circuit data.numGates)
    (l : ℕ) (hl : 0 < l)
    (h_depth : 1 ≤ c_top.depth)
    (hDNF_fn : ∀ i, ∃ φ : DNF n, φ.width ≤ l ∧
      (∀ x, φ.eval x = (data.gates i).eval x) ∧
      (∀ t ∈ φ, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂) ∧
      (∀ t ∈ φ, t.Nodup))
    (hCNF_fn : ∀ i, ∃ ψ : CNF n, ψ.width ≤ l ∧
      ∀ x, CNF.eval ψ x = (data.gates i).eval x) :
    ∃ (data' : Layer2Data n) (c_top' : Circuit data'.numGates),
      c_top'.depth ≤ c_top.depth - 1 ∧ data'.width ≤ l ∧
      (∀ x, c_top.eval (fun i => (data.gates i).eval x) =
            c_top'.eval (fun j => (data'.gates j).eval x)) := by
  by_cases h1 : c_top.depth ≤ 1
  · obtain ⟨data', c_top', hd, hw, he⟩ := absorbOneLevel_depth1 data c_top l hl h1 h_depth
      hDNF_fn hCNF_fn
    exact ⟨data', c_top', by omega, hw, he⟩
  · push_neg at h1
    obtain ⟨data', c_top', hd, hw, he⟩ := absorbOneLevel_general data c_top l hl
      (by omega) hDNF_fn hCNF_fn
    exact ⟨data', c_top', by omega, hw, he⟩

end LMN
end