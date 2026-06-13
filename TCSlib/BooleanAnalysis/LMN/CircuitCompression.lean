import TCSlib.BooleanAnalysis.LMN.GateSwitching
import Mathlib

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

open BoolCircuit SwitchingLemma2 SwitchingBernoulli LMN
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
Width of a term list is bounded iff all terms have bounded width.
-/
private lemma width_le_iff_forall {ts : List (Term n)} {l : ℕ} :
    (ts.map Term.width).foldr max 0 ≤ l ↔ ∀ t ∈ ts, t.width ≤ l := by
  induction' ts with t ts ihizing l;
  · norm_num +zetaDelta at *;
  · grind +splitImp

/-
**CNF concatenation preserves width.**

    If CNFs ψ₁, …, ψₛ each have width ≤ l, then their concatenation
    (which computes the conjunction of all clauses from all CNFs) also
    has width ≤ l.
-/
lemma cnf_concat_width_le (cnfs : List (CNF n)) (l : ℕ)
    (h : ∀ ψ ∈ cnfs, CNF.width ψ ≤ l) :
    CNF.width (listConcat cnfs) ≤ l := by
  induction' cnfs with ψ cnfs ih;
  · exact Nat.zero_le _;
  · simp_all +decide [ listConcat ];
    unfold CNF.width at *;
    induction ψ <;> aesop

/-
**CNF concatenation evaluates as conjunction.**
-/
lemma cnf_concat_eval (cnfs : List (CNF n)) (x : Fin n → Bool) :
    CNF.eval (listConcat cnfs) x = cnfs.all (fun ψ => CNF.eval ψ x) := by
  induction cnfs with
  | nil => simp [listConcat, CNF.eval]
  | cons head tail ih =>
      simp only [listConcat, List.all_append, CNF.eval]
      simp_all +decide [CNF.eval]

/-
**DNF concatenation preserves width.**
-/
lemma dnf_concat_width_le (dnfs : List (DNF n)) (l : ℕ)
    (h : ∀ φ ∈ dnfs, DNF.width φ ≤ l) :
    DNF.width (listConcat dnfs) ≤ l := by
  convert cnf_concat_width_le ( List.map ( fun φ => φ.map ( fun clause => clause.map ( fun l => ⟨ l.var, !l.neg ⟩ ) ) ) dnfs ) l ?_ using 1;
  · have h_width_eq : ∀ cnfs : List (CNF n), CNF.width (listConcat cnfs) = DNF.width (listConcat (List.map (fun φ => φ.map (fun clause => clause.map (fun l => ⟨l.var, !l.neg⟩))) cnfs)) := by
      -- The width of a CNF is the maximum length of its clauses, and the width of a DNF is the maximum length of its terms. Since each clause in the CNF becomes a term in the DNF by negating the literals, the lengths of the clauses and terms are the same. Therefore, the maximum length (width) should be the same.
      intros cnfs
      simp [CNF.width, DNF.width];
      induction' cnfs with cnfs ih <;> simp_all +decide [ listConcat ];
      congr! 2;
      ext; simp [Term.width];
    convert h_width_eq ( List.map ( fun φ => φ.map ( fun clause => clause.map ( fun l => ⟨ l.var, !l.neg ⟩ ) ) ) dnfs ) |> Eq.symm using 1;
    convert rfl using 2;
    refine' congr_arg _ ( List.ext_get _ _ ) <;> aesop;
  · simp +zetaDelta at *;
    intro φ hφ;
    convert h φ hφ using 1;
    convert cnfToDualDNF_width φ using 1

/-
**DNF concatenation evaluates as disjunction.**
-/
lemma dnf_concat_eval (dnfs : List (DNF n)) (x : Fin n → Bool) :
    DNF.eval (listConcat dnfs) x = dnfs.any (fun φ => DNF.eval φ x) := by
  induction' dnfs with dnfs ih <;> simp_all +decide [ DNF.eval ];
  · tauto;
  · rw [ ← ‹ ( ( listConcat ih ).any fun t => t.eval x ) = ih.any fun φ => List.any φ fun t => t.eval x ›, listConcat ] ; simp +decide [ List.any_append ] ;

/-
**Circuit compression for CNFs under AND (Step 6, AND case).**

    If a layer-3 AND gate has s₂ children, and each child computes a function
    that can be expressed as a CNF of width ≤ l, then the AND of all children
    can be expressed as a single CNF of width ≤ l.

    Proof: Each child function fᵢ has a CNF ψᵢ with width ≤ l.
    Define ψ = ψ₁ ++ ψ₂ ++ ⋯ ++ ψₛ (concatenation of all clause lists).
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
  refine' ⟨ LMN.listConcat ( List.map ψ children ), _, _ ⟩;
  · exact cnf_concat_width_le _ _ fun ψ' hψ' => by aesop;
  · convert cnf_concat_eval ( List.map ψ children ) using 1;
    simp +decide [ List.all_map, hψ₂ ];
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
  refine' ⟨ LMN.listConcat ( children.map φ ), _, _ ⟩ <;> simp_all +decide [ LMN.dnf_concat_width_le, LMN.dnf_concat_eval ];
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
    (hnd : ∀ i, ∀ t ∈ gates i, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ i, ∀ t ∈ gates i, t.Nodup)
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
    (hnd : ∀ i, ∀ t ∈ gates i, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ i, ∀ t ∈ gates i, t.Nodup)
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
  unfold bernoulliRestrProb; simp +decide [ bernoulliRestrWeight_sum_one p hp hp1 ] ;
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
    (hnd : ∀ i, ∀ t ∈ gates i, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ i, ∀ t ∈ gates i, t.Nodup)
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