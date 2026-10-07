import TCSlib.Complexity.CircuitComplexity.Basic
import TCSlib.BooleanAnalysis.LMN.GateSwitching

/-!
# Circuit Compression and One-Step Reduction (Steps 6–7 of LMN)

## Step 6: Circuit Compression

If all nodes at layer 2 of a depth-d circuit can be switched to width-l CNFs,
then layers 2 and 3 can be compressed, producing a depth-(d-1) circuit of
width at most l.

The key structural observation is: if layer 3 is an AND gate and each of its
layer-2 children (originally DNFs) has been replaced by a width-l CNF
(= AND of OR-clauses), then the layer-3 gate computes
AND(AND(clauses₁), AND(clauses₂), …) = AND(all clauses),
collapsing two layers into one. Dually, OR of DNFs collapses similarly.

## Step 7: One-Step Reduction

After a Bernoulli(1/(40w)) random restriction, with high probability:
- All layer-2 gates become width-l CNFs (by the switching lemma union bound, Step 5)
- The circuit compresses to depth-(d−1) and width ≤ l (by Step 6)

The failure probability is at most s₂ · ((1/2)^l + exp(-np/3)), where s₂ is the
number of layer-2 gates.
-/

open BoolCircuit SwitchingLemma SwitchingBernoulli LMN
open Classical in
attribute [local instance] Classical.propDecidable
noncomputable section

namespace LMN

variable {n : ℕ}

/-- Concatenation of a list of lists, compatible across Lean versions. -/
def listConcat {α : Type u} : List (List α) → List α
  | [] => []
  | l :: ls => l ++ listConcat ls

/-! ## Step 6: Circuit Compression

The compression relies on the algebraic identities:
- AND(AND(A₁), AND(A₂), …) = AND(A₁ ∪ A₂ ∪ …)  [AND-of-ANDs flattening]
- OR(OR(B₁), OR(B₂), …) = OR(B₁ ∪ B₂ ∪ …)      [OR-of-ORs flattening]

These allow merging two adjacent layers of the same gate type into one.
When layer-2 DNF gates are replaced by width-l CNFs, the layer-3 AND gate
(which was previously over DNFs) is now over CNFs = AND-of-ORs. The
AND-of-ANDs identity collapses layers 2 and 3 into a single CNF layer. -/

/-
Width of a depth-2 shape is bounded iff every literal list in it has bounded width.
-/
private lemma width_le_iff_forall {F : Depth2 n} {l : ℕ} :
    Depth2.width F ≤ l ↔ ∀ t ∈ F, t.width ≤ l := by
  induction F with
  | nil => simp [Depth2.width]
  | cons t F ih =>
    simp only [Depth2.width, List.map_cons, List.foldr_cons, max_le_iff, List.mem_cons,
      forall_eq_or_imp] at ih ⊢
    rw [ih]

private lemma mem_listConcat {α : Type u} {ls : List (List α)} {a : α} :
    a ∈ listConcat ls ↔ ∃ l ∈ ls, a ∈ l := by
  induction ls with
  | nil => simp [listConcat]
  | cons l ls ih => simp [listConcat, ih]

/-- The conjunction of a list of CNFs: concatenate their clause lists. -/
def cnfConcat (cnfs : List (CNF n)) : CNF n := ⟨listConcat (cnfs.map CNF.clauses)⟩

/-- The disjunction of a list of DNFs: concatenate their term lists. -/
def dnfConcat (dnfs : List (DNF n)) : DNF n := ⟨listConcat (dnfs.map DNF.terms)⟩

/-
**CNF concatenation preserves width.**

    If CNFs ψ₁, …, ψₛ each have width ≤ l, then their concatenation
    (which computes the conjunction of all clauses from all CNFs) also
    has width ≤ l.
-/
lemma cnf_concat_width_le (cnfs : List (CNF n)) (l : ℕ)
    (h : ∀ ψ ∈ cnfs, CNF.width ψ ≤ l) :
    CNF.width (cnfConcat cnfs) ≤ l := by
  simp only [cnfConcat, CNF.width_mk, width_le_iff_forall, mem_listConcat, List.mem_map]
  rintro c ⟨_, ⟨ψ, hψ, rfl⟩, hc⟩
  exact width_le_iff_forall.mp (h ψ hψ) c hc

/-
**CNF concatenation evaluates as conjunction.**
-/
lemma cnf_concat_eval (cnfs : List (CNF n)) (x : Fin n → Bool) :
    CNF.eval (cnfConcat cnfs) x = cnfs.all (fun ψ => CNF.eval ψ x) := by
  induction cnfs with
  | nil => rfl
  | cons ψ cnfs ih =>
    simp only [cnfConcat, CNF.eval_mk, List.map_cons, listConcat, List.all_append,
      List.all_cons] at ih ⊢
    rw [ih]; rfl

/-
**DNF concatenation preserves width.**
-/
lemma dnf_concat_width_le (dnfs : List (DNF n)) (l : ℕ)
    (h : ∀ φ ∈ dnfs, DNF.width φ ≤ l) :
    DNF.width (dnfConcat dnfs) ≤ l := by
  simp only [dnfConcat, DNF.width_mk, width_le_iff_forall, mem_listConcat, List.mem_map]
  rintro t ⟨_, ⟨φ, hφ, rfl⟩, ht⟩
  exact width_le_iff_forall.mp (h φ hφ) t ht

/-
**DNF concatenation evaluates as disjunction.**
-/
lemma dnf_concat_eval (dnfs : List (DNF n)) (x : Fin n → Bool) :
    DNF.eval (dnfConcat dnfs) x = dnfs.any (fun φ => DNF.eval φ x) := by
  induction dnfs with
  | nil => rfl
  | cons φ dnfs ih =>
    simp only [dnfConcat, DNF.eval_mk, List.map_cons, listConcat, List.any_append,
      List.any_cons] at ih ⊢
    rw [ih]; rfl

/-
**Circuit compression for CNFs under AND (Step 6, AND case).**

    If a layer-3 AND gate has s₂ children, and each child computes a function
    that can be expressed as a CNF of width ≤ l, then the AND of all children
    can be expressed as a single CNF of width ≤ l.

    Proof: Each child function fᵢ has a CNF ψᵢ with width ≤ l.
    Define ψ = cnfConcat [ψ₁, …, ψₛ] (concatenation of all clause lists).
    Then ψ.eval x = (ψ₁.eval x) && (ψ₂.eval x) && ⋯ = (f₁ x) && ⋯
    and ψ.width ≤ l since each ψᵢ.width ≤ l.

    This eliminates one layer: the AND gate at layer 3 and the CNF gates
    at layer 2 merge into a single CNF gate, reducing circuit depth by 1.
-/
theorem compression_and_of_cnfs
    (children : List ((Fin n → Bool) → Bool))
    (l : ℕ)
    (h_cnf : ∀ f ∈ children, ∃ ψ : CNF n, CNF.width ψ ≤ l ∧
      ∀ x, CNF.eval ψ x = f x) :
    ∃ ψ : CNF n, CNF.width ψ ≤ l ∧
      ∀ x, CNF.eval ψ x = children.all (fun f => f x) := by
  choose! ψ hψ₁ hψ₂ using h_cnf;
  refine' ⟨ cnfConcat ( List.map ψ children ), _, _ ⟩;
  · exact cnf_concat_width_le _ _ fun ψ' hψ' => by aesop;
  · convert cnf_concat_eval ( List.map ψ children ) using 1;
    simp +decide [ List.all_map ];
    grind

/-
**Circuit compression for DNFs under OR (Step 6, OR case).**

    Dual of `compression_and_of_cnfs`: if a layer-3 OR gate has children
    that are each expressible as width-l DNFs, then the overall gate
    can be expressed as a single DNF of width ≤ l.
-/
theorem compression_or_of_dnfs
    (children : List ((Fin n → Bool) → Bool))
    (l : ℕ)
    (h_dnf : ∀ f ∈ children, ∃ φ : DNF n, DNF.width φ ≤ l ∧
      ∀ x, DNF.eval φ x = f x) :
    ∃ φ : DNF n, DNF.width φ ≤ l ∧
      ∀ x, DNF.eval φ x = children.any (fun f => f x) := by
  choose! φ hφ using h_dnf;
  refine' ⟨ dnfConcat ( children.map φ ), _, _ ⟩ <;> simp_all +decide [ LMN.dnf_concat_width_le, LMN.dnf_concat_eval ];
  grind

/-! ## Step 7: One-Step Reduction -/

/-
**One-step reduction failure bound (Step 7).**

    The probability that some gate FAILS to have a width-l CNF
    representation is at most s₂ · ((1/2)^l + exp(-np/3)).

    When this failure event does NOT occur, Step 6 compression applies:
    layers 2 and 3 merge, and the circuit reduces to depth-(d-1) with
    width ≤ l.
-/
theorem one_step_reduction_failure_bound
    (gates : Fin s₂ → DNF n) (w l : ℕ)
    (hw : ∀ i, (gates i).width ≤ w) (hw_pos : 0 < w)
    (hnd : ∀ i, ∀ t ∈ (gates i).terms, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ i, ∀ t ∈ (gates i).terms, t.Nodup)
    (hn : 0 < n)
    (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1 / (40 * ↑w)) (hp1 : p ≤ 1) :
    bernoulliRestrProb p
      (fun ρ => ¬ ∀ i : Fin s₂,
        ∃ ψ : CNF n, CNF.width ψ ≤ l ∧ ∀ x, CNF.eval ψ x = restrictFn (gates i).eval ρ x)
    ≤ ↑s₂ * ((1 / 2 : ℝ) ^ l + Real.exp (-(↑n * p / 3))) := by
  convert layer2_cnf_replaceability_union_bound gates w l hw hw_pos hnd hnodup hn p hp_pos hp_le hp1 using 3;
  simp +decide only [not_forall]

/-
**One-step dtDepth bound (Step 7, decision-tree depth form).**

    Under a Bernoulli(p) restriction with p ≤ 1/(40w), the probability that
    ALL s₂ layer-2 gates have dtDepth ≤ l is at least
    1 - s₂ · ((1/2)^l + exp(-np/3)).

    When dtDepth ≤ l for all gates, each gate can be replaced by both a
    width-l DNF and a width-l CNF (by `dtDepth_le_implies_small_dnf_cnf`),
    enabling the depth compression of Step 6.

    This is a direct corollary of `switching_bernoulli_union_bound`.
-/
theorem one_step_dtDepth_bound
    (gates : Fin s₂ → DNF n) (w l : ℕ)
    (hw : ∀ i, (gates i).width ≤ w) (hw_pos : 0 < w)
    (hnd : ∀ i, ∀ t ∈ (gates i).terms, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ i, ∀ t ∈ (gates i).terms, t.Nodup)
    (hn : 0 < n)
    (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1 / (40 * ↑w)) (hp1 : p ≤ 1) :
    bernoulliRestrProb p
      (fun ρ => ∀ i : Fin s₂, dtDepth (restrictFn (gates i).eval ρ) ≤ l)
    ≥ 1 - ↑s₂ * ((1 / 2 : ℝ) ^ l + Real.exp (-(↑n * p / 3))) := by
  have h_complement : bernoulliRestrProb p (fun ρ => ∃ i : Fin s₂, dtDepth (restrictFn (gates i).eval ρ) > l) ≤ s₂ * ((1 / 2 : ℝ) ^ l + Real.exp (-(n * p / 3))) := by
    convert switching_bernoulli_union_bound gates w l hw hw_pos hnd hnodup hn p hp_pos hp_le hp1 using 1;
  have h_total : bernoulliRestrProb p (fun ρ => ∀ i : Fin s₂, dtDepth (restrictFn (gates i).eval ρ) ≤ l) + bernoulliRestrProb p (fun ρ => ∃ i : Fin s₂, dtDepth (restrictFn (gates i).eval ρ) > l) = 1 := by
    unfold bernoulliRestrProb;
    rw [ ← Finset.sum_add_distrib, Finset.sum_congr rfl fun x hx => ?_, bernoulliRestrWeight_sum_one ];
    exact p;
    · positivity;
    · linarith;
    · by_cases h : ∀ i : Fin s₂, dtDepth ( restrictFn ( gates i ).eval x ) ≤ l <;> simp +decide [ h ];
  linarith

/-
Complement probability: Pr[A] + Pr[¬A] = 1.
-/
lemma bernoulliRestrProb_complement (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Restriction n → Prop) [DecidablePred A] :
    bernoulliRestrProb p A + bernoulliRestrProb p (fun ρ => ¬ A ρ) = 1 := by
  unfold bernoulliRestrProb; simp +decide ;
  rw [ ← Finset.sum_add_distrib, Finset.sum_congr rfl fun _ _ => by aesop, bernoulliRestrWeight_sum_one p hp hp1 ]

/-
**One-step reduction with compression (Steps 6+7 combined).**

    After a Bernoulli(1/(40w)) restriction on a circuit with s₂
    width-w DNF gates at layer 2, with probability at least
    1 - s₂ · ((1/2)^l + exp(-np/3)):
    - All layer-2 gates become width-l CNFs (Step 5/7)
    - The circuit compresses to depth-(d-1) with width ≤ l (Step 6)
-/
theorem one_step_reduction_with_compression
    (gates : Fin s₂ → DNF n) (w l : ℕ)
    (hw : ∀ i, (gates i).width ≤ w) (hw_pos : 0 < w)
    (hnd : ∀ i, ∀ t ∈ (gates i).terms, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ i, ∀ t ∈ (gates i).terms, t.Nodup)
    (hn : 0 < n)
    (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1 / (40 * ↑w)) (hp1 : p ≤ 1) :
    bernoulliRestrProb p
      (fun ρ => ∀ i : Fin s₂,
        ∃ ψ : CNF n, CNF.width ψ ≤ l ∧ ∀ x, CNF.eval ψ x = restrictFn (gates i).eval ρ x)
    ≥ 1 - ↑s₂ * ((1 / 2 : ℝ) ^ l + Real.exp (-(↑n * p / 3))) := by
  have := one_step_reduction_failure_bound gates w l hw hw_pos hnd hnodup hn p hp_pos hp_le hp1;
  sorry -- TODO: needs bernoulliRestrProb complement lemma: P(E) ≥ 1 - P(¬E)

end LMN
end