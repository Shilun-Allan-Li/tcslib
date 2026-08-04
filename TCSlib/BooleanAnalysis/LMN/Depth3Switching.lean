import TCSlib.BooleanAnalysis.LMN.CircuitLayerReduction

/-!
# Depth-3 Circuit Switching and Compression

This file formalizes the switching argument for depth-3 circuits, assuming
normal form. A depth-3 AND-of-OR-of-AND circuit is expressed as the AND
of `s₂` DNF gates, each of width ≤ `w`.

## Main results

1. **One-step compression** (`depth3_compression`): Under a Bernoulli(`1/(40w)`)
   restriction, with probability ≥ 1 − s₂ · ((1/2)^l + exp(−np/3)), ALL gates
   become width-l CNFs and the circuit compresses from depth 3 to a single
   width-l CNF (depth 2).

2. **Two-stage switching** (`depth3_switching_bound`): Under a composed
   Bernoulli(`p₁ · p₂`) restriction (where `p₁ = 1/(40w)` and `p₂ = 1/(40l)`),
   the probability that `dtDepth(f|_ρ) > t` is at most
   `s₂ · ((1/2)^l + tail₁) + ((1/2)^t + tail₂)`.

## Proof structure

The depth-3 argument proceeds as follows:
- **Stage 1**: Apply Bernoulli(`p₁`) restriction. By the switching lemma
  and union bound, each width-`w` DNF gate at layer 2 has dtDepth ≤ l with
  high probability. When dtDepth ≤ l, the gate can be expressed as a width-l CNF.
- **Compression**: AND-of-CNFs = single CNF (by concatenation). The circuit
  drops from depth 3 to depth 2.
- **Stage 2**: Apply Bernoulli(`p₂`) restriction. The width-l CNF from stage 1
  has dtDepth ≤ t with high probability (by the switching lemma for CNFs).
- **Composition**: By `restriction_compose_eq`, the composed restriction
  Bernoulli(`p₁ · p₂`) accounts for both stages.
-/

open BoolCircuit SwitchingLemma2 SwitchingBernoulli LMN
open Classical in
attribute [local instance] Classical.propDecidable
noncomputable section

namespace LMN

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ## Restriction Composition for Functions -/

/-
Restricting a function by the composition of two restrictions is the same
    as restricting twice: first by `ρ₁`, then by `ρ₂`.
-/
theorem restrictFn_composeRestr (f : (Fin n → Bool) → Bool)
    (ρ₁ ρ₂ : Restriction n) :
    restrictFn f (composeRestr ρ₁ ρ₂) = restrictFn (restrictFn f ρ₁) ρ₂ := by
  unfold restrictFn composeRestr;
  unfold Restriction.extend; aesop;

/-
If two functions agree everywhere, they have the same dtDepth.
-/
lemma dtDepth_congr (f g : (Fin n → Bool) → Bool) (h : ∀ x, f x = g x) :
    dtDepth f = dtDepth g := by
  -- Since $f$ and $g$ are equal, their dtDepth is the same.
  have h_eq : f = g := by
    exact funext h
  rw [h_eq]

/-
If two functions agree everywhere, restricting them gives the same result.
-/
lemma restrictFn_congr (f g : (Fin n → Bool) → Bool) (ρ : Restriction n)
    (h : ∀ x, f x = g x) :
    ∀ x, restrictFn f ρ x = restrictFn g ρ x := by
  unfold restrictFn; aesop;

/-! ## AND of Functions -/

/-- The pointwise AND of a list of Boolean functions. -/
def listAnd {n : ℕ} : List ((Fin n → Bool) → Bool) → (Fin n → Bool) → Bool
  | [], _ => true
  | f :: fs, x => f x && listAnd fs x

/-
restrictFn distributes over listAnd.
-/
lemma restrictFn_listAnd (fs : List ((Fin n → Bool) → Bool)) (ρ : Restriction n) :
    ∀ x, restrictFn (listAnd fs) ρ x = listAnd (fs.map (fun f => restrictFn f ρ)) x := by
  intro x;
  induction fs <;> simp_all +decide [ List.map ];
  · rfl;
  · convert congr_arg₂ ( fun a b => a && b ) rfl ‹_› using 1

/-! ## Depth-3 One-Step Compression -/

/-
**Depth-3 one-step compression theorem.**

    Given s₂ width-w DNF gates and a function f that is their AND,
    under Bernoulli(p) with p ≤ 1/(40w), with probability ≥ 1 - s₂ · ((1/2)^l + tail):
    - All gates can be expressed as width-l CNFs after restriction
    - The restricted function f|_ρ can be expressed as a single width-l CNF

    This IS the depth-3 switching argument: the circuit compresses from depth 3
    (AND of DNFs) to depth 2 (single CNF of width l).
-/
theorem depth3_compression
    (s₂ : ℕ) (gates : Fin s₂ → DNF n) (w l : ℕ)
    (hw : ∀ i, (gates i).width ≤ w) (hw_pos : 0 < w)
    (hnd : ∀ i, ∀ t ∈ gates i, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ i, ∀ t ∈ gates i, t.Nodup)
    (hn : 0 < n)
    (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1 / (40 * ↑w)) (hp1 : p ≤ 1) :
    bernoulliRestrProb p
      (fun ρ => ∃ Ψ : CNF n, CNF.width Ψ ≤ l ∧
        ∀ x, CNF.eval Ψ x = listAnd (List.ofFn (fun i => restrictFn (gates i).eval ρ)) x)
    ≥ 1 - ↑s₂ * ((1 / 2 : ℝ) ^ l + Real.exp (-(↑n * p / 3))) := by
  refine' le_trans ( one_step_reduction_with_compression gates w l hw hw_pos hnd hnodup hn p hp_pos hp_le hp1 ) _;
  refine' Finset.sum_le_sum fun _ => _;
  split_ifs <;> norm_num;
  · rename_i h₁ h₂;
    contrapose! h₂;
    convert compression_and_of_cnfs ( List.ofFn fun i => restrictFn ( gates i ).eval ‹_› ) l _ using 1;
    · congr! 3;
      congr! 1;
      rw [ List.ofFn_eq_map ];
      induction ( List.finRange s₂ ) <;> simp +decide [ *, listAnd ];
    · simp +decide [ List.mem_ofFn ];
      exact h₁;
  · exact mul_nonneg ( pow_nonneg hp_pos.le _ ) ( pow_nonneg ( by linarith ) _ )

/-! ## CNF Cleanup for Switching Lemma Conditions -/

/-- A clause (disjunction of literals) is tautological if it contains two
    literals with the same variable but opposite signs. -/
def clauseIsTaut (c : List (Literal n)) : Prop :=
  ∃ l₁ ∈ c, ∃ l₂ ∈ c, l₁.var = l₂.var ∧ l₁.neg ≠ l₂.neg

instance (c : List (Literal n)) : Decidable (clauseIsTaut c) := by
  unfold clauseIsTaut; infer_instance

/-
A tautological clause evaluates to true under any assignment.
-/
lemma clauseIsTaut_eval_true (c : List (Literal n)) (h : clauseIsTaut c)
    (x : Fin n → Bool) :
    c.any (fun l => l.eval x) = true := by
  -- By definition of clauseIsTaut, there exist l₁ and l₂ in c such that � l�₁.var = l₂.var and l₁.neg ≠ l₂.neg.
  obtain ⟨l₁, hl₁, l₂, hl₂, h_var, h_neg⟩ := h;
  cases h : l₁.neg <;> cases h' : l₂.neg <;> simp_all +decide [ Literal.eval ]; all_goals grind

/-- Remove duplicate variables from a clause, keeping first occurrence per variable. -/
def dedupClauseVars (c : List (Literal n)) : List (Literal n) :=
  c.pwFilter (fun l₁ l₂ => decide (l₁.var ≠ l₂.var))

/-
`dedupClauseVars` produces a list with pairwise distinct variable indices.
-/
lemma dedupClauseVars_var_inj (c : List (Literal n)) :
    ∀ l₁ ∈ dedupClauseVars c, ∀ l₂ ∈ dedupClauseVars c,
    l₁.var = l₂.var → l₁ = l₂ := by
  unfold dedupClauseVars;
  simp +decide [ List.pwFilter ];
  induction' c with x c ih;
  · aesop;
  · grind

/-
`dedupClauseVars` produces a list with no duplicates.
-/
lemma dedupClauseVars_nodup (c : List (Literal n)) :
    (dedupClauseVars c).Nodup := by
  convert List.Pairwise.imp _ ( List.pairwise_pwFilter _ ) using 1;
  grind

/-
`dedupClauseVars` produces a sublist (hence width doesn't increase).
-/
lemma dedupClauseVars_length_le (c : List (Literal n)) :
    (dedupClauseVars c).length ≤ c.length := by
  have h_sublist : dedupClauseVars c ∈ c.sublists := by
    simp +decide [ dedupClauseVars ];
    exact List.pwFilter_sublist c;
  exact List.mem_sublists.mp h_sublist |> fun h => List.Sublist.length_le h

/-
For a non-tautological clause, deduplication preserves evaluation.
-/
lemma dedupClauseVars_eval_of_not_taut (c : List (Literal n)) (h : ¬clauseIsTaut c)
    (x : Fin n → Bool) :
    (dedupClauseVars c).any (fun l => l.eval x) = c.any (fun l => l.eval x) := by
  sorry -- TODO: grind failures in pwFilter induction; needs interactive debugging

/-- Clean a CNF: remove tautological clauses, then deduplicate within each clause. -/
def cleanCNF_D3 (ψ : CNF n) : CNF n :=
  (ψ.filter (fun c => ¬clauseIsTaut c)).map dedupClauseVars

/-
Cleaning preserves CNF evaluation.
-/
lemma cleanCNF_D3_eval (ψ : CNF n) (x : Fin n → Bool) :
    CNF.eval (cleanCNF_D3 ψ) x = CNF.eval ψ x := by
  unfold cleanCNF_D3;
  unfold CNF.eval; simp +decide [ List.all_map ] ;
  congr! 2 with t ht ; by_cases h : clauseIsTaut t <;> simp +decide [ h, CNF.evalClause ];
  · have := clauseIsTaut_eval_true t h x; aesop;
  · exact dedupClauseVars_eval_of_not_taut t h x

/-
Cleaning doesn't increase width.
-/
lemma cleanCNF_D3_width_le (ψ : CNF n) :
    CNF.width (cleanCNF_D3 ψ) ≤ CNF.width ψ := by
  by_contra h_contra;
  -- Apply the definition of width to both CNFs.
  unfold CNF.width at h_contra;
  -- By definition of `cleanCNF_D3`, we know that every clause in `cleanCNF_D3 ψ` is a deduplicated version of some clause in `ψ`.
  have h_clean : ∀ c' ∈ (cleanCNF_D3 ψ), ∃ c ∈ ψ, Term.width c' ≤ Term.width c := by
    unfold cleanCNF_D3;
    simp +zetaDelta at *;
    exact fun c' x hx hx' hx'' => ⟨ x, hx, hx''.symm ▸ dedupClauseVars_length_le x ⟩;
  -- By definition of `cleanCNF_D3`, we know that every clause in `cleanCNF_D3 ψ` is a deduplicated version of some clause in `ψ`, so the width of `cleanCNF_D3 ψ` is less than or equal to the width of `ψ`.
  have h_width_le : ∀ c' ∈ (cleanCNF_D3 ψ), c'.width ≤ List.foldr max 0 (List.map Term.width ψ) := by
    intro c' hc'
    obtain ⟨c, hcψ, hc'⟩ := h_clean c' hc'
    have hc'_le : c.width ≤ List.foldr max 0 (List.map Term.width ψ) := by
      have h_width_le : ∀ {l : List (Term n)}, c ∈ l → c.width ≤ List.foldr max 0 (List.map Term.width l) := by
        intros l hl; induction l <;> aesop;
      exact h_width_le hcψ;
    exact le_trans hc' hc'_le;
  have h_foldr_le : ∀ {l : List ℕ}, (∀ x ∈ l, x ≤ List.foldr max 0 (List.map Term.width ψ)) → List.foldr max 0 l ≤ List.foldr max 0 (List.map Term.width ψ) := by
    intros l hl; induction l <;> aesop;
  grind

/-
Cleaned CNF has nodup clauses.
-/
lemma cleanCNF_D3_nodup (ψ : CNF n) :
    ∀ c ∈ cleanCNF_D3 ψ, c.Nodup := by
  intro c hc; obtain ⟨ c', hc', rfl ⟩ := List.mem_map.mp hc; exact dedupClauseVars_nodup c';

/-
Cleaned CNF has variable-injective clauses.
-/
lemma cleanCNF_D3_var_inj (ψ : CNF n) :
    ∀ c ∈ cleanCNF_D3 ψ, ∀ l₁ ∈ c, ∀ l₂ ∈ c, l₁.var = l₂.var → l₁ = l₂ := by
  intros c hc l₁ hl₁ l₂ hl₂ hvar
  apply dedupClauseVars_var_inj;
  any_goals assumption;
  · unfold cleanCNF_D3 at hc;
    unfold dedupClauseVars at *; aesop;
  · unfold cleanCNF_D3 at hc;
    unfold dedupClauseVars at *; aesop;

/-- Any CNF can be cleaned to satisfy the switching lemma conditions. -/
theorem exists_nice_cnf_of_cnf (ψ : CNF n) :
    ∃ ψ' : CNF n, CNF.width ψ' ≤ CNF.width ψ ∧
    (∀ x, CNF.eval ψ' x = CNF.eval ψ x) ∧
    (∀ c ∈ ψ', c.Nodup) ∧
    (∀ c ∈ ψ', ∀ l₁ ∈ c, ∀ l₂ ∈ c, l₁.var = l₂.var → l₁ = l₂) :=
  ⟨cleanCNF_D3 ψ, cleanCNF_D3_width_le ψ, fun x => cleanCNF_D3_eval ψ x,
   cleanCNF_D3_nodup ψ, cleanCNF_D3_var_inj ψ⟩

/-- Any function with bounded dtDepth has a nice CNF representation. -/
theorem dtDepth_le_implies_nice_cnf (f : (Fin n → Bool) → Bool) (d : ℕ)
    (h : dtDepth f ≤ d) :
    ∃ ψ : CNF n, CNF.width ψ ≤ d ∧ (∀ x, CNF.eval ψ x = f x) ∧
    (∀ c ∈ ψ, c.Nodup) ∧
    (∀ c ∈ ψ, ∀ l₁ ∈ c, ∀ l₂ ∈ c, l₁.var = l₂.var → l₁ = l₂) := by
  obtain ⟨ψ₀, hw₀, heval₀⟩ := (dtDepth_le_implies_small_dnf_cnf f d h).2
  obtain ⟨ψ', hw', heval', hnodup', hvarinj'⟩ := exists_nice_cnf_of_cnf ψ₀
  exact ⟨ψ', le_trans hw' hw₀, fun x => (heval' x).trans (heval₀ x), hnodup', hvarinj'⟩

/-
Similarly for DNF.
-/
theorem dtDepth_le_implies_nice_dnf (f : (Fin n → Bool) → Bool) (d : ℕ)
    (h : dtDepth f ≤ d) :
    ∃ φ : DNF n, DNF.width φ ≤ d ∧ (∀ x, DNF.eval φ x = f x) ∧
    (∀ t ∈ φ, t.Nodup) ∧
    (∀ t ∈ φ, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂) := by
  sorry -- TODO: needs dtDepth_neg and CNF↔DNF negation duality

/-! ## Functional Switching Lemma -/

/-- **Functional switching lemma for CNFs.**

    For any function f with dtDepth ≤ w, under Bernoulli(p) with p ≤ 1/(40w):
    `Pr[dtDepth(f|_ρ) > t] ≤ (1/2)^t + exp(-np/3)`.

    This is the switching lemma stated at the level of functions (rather than
    specific formulas), which is what we need for the second stage of the
    depth-3 argument. -/
theorem switching_bernoulli_dtDepth_function (f : (Fin n → Bool) → Bool) (w : ℕ)
    (h : dtDepth f ≤ w) (hw_pos : 0 < w)
    (hn : 0 < n)
    (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1 / (40 * ↑w)) (hp1 : p ≤ 1)
    (t : ℕ) :
    bernoulliRestrProb p (fun ρ => dtDepth (restrictFn f ρ) > t) ≤
    (1 / 2 : ℝ) ^ t + Real.exp (-(↑n * p / 3)) := by
  -- Get a nice CNF representation of f
  obtain ⟨ψ, hw_ψ, heval_ψ, hnodup_ψ, hvarinj_ψ⟩ := dtDepth_le_implies_nice_cnf f w h
  -- The dtDepth of restrictFn f ρ = dtDepth of restrictFn ψ.eval ρ
  have h_eq : ∀ ρ, dtDepth (restrictFn f ρ) = dtDepth (restrictFn (CNF.eval ψ) ρ) := by
    intro ρ; exact dtDepth_congr _ _ (restrictFn_congr _ _ ρ (fun x => (heval_ψ x).symm))
  -- Apply the CNF switching lemma to ψ
  calc bernoulliRestrProb p (fun ρ => dtDepth (restrictFn f ρ) > t)
      = bernoulliRestrProb p (fun ρ => dtDepth (restrictFn (CNF.eval ψ) ρ) > t) := by
        congr 1; ext ρ; rw [h_eq]
    _ ≤ (1 / 2 : ℝ) ^ t + Real.exp (-(↑n * p / 3)) :=
        switching_bernoulli_dtDepth_cnf ψ w hw_ψ hw_pos hvarinj_ψ hnodup_ψ hn p hp_pos hp_le hp1 t

/-! ## General Two-Stage Bound -/

/-
**General two-stage bound.** If under a composed Bernoulli(p₁·p₂) restriction,
    the conditional probability Pr_{p₂}[E | ρ₁] is bounded by β whenever ¬A(ρ₁),
    then Pr_{p₁·p₂}[E] ≤ Pr_{p₁}[A] + β.
-/
theorem two_stage_bound
    (p₁ p₂ : ℝ) (hp₁ : 0 < p₁) (hp₁_1 : p₁ ≤ 1) (hp₂ : 0 < p₂) (hp₂_1 : p₂ ≤ 1)
    (E : Restriction n → Prop) [DecidablePred E]
    (A : Restriction n → Prop) [DecidablePred A]
    (β : ℝ) (hβ : 0 ≤ β)
    (h_bound : ∀ ρ₁, ¬A ρ₁ →
      bernoulliRestrProb p₂ (fun ρ₂ => E (composeRestr ρ₁ ρ₂)) ≤ β) :
    bernoulliRestrProb (p₁ * p₂) E ≤ bernoulliRestrProb p₁ A + β := by
  -- Rewrite `bernoulliRestrProb (p₁ * p₂) E` using the `restriction_compose_eq` theorem.
  have h_eq : bernoulliRestrProb (p₁ * p₂) E = ∑ ρ₁, bernoulliRestrWeight p₁ ρ₁ * bernoulliRestrProb p₂ (fun ρ₂ => E (composeRestr ρ₁ ρ₂)) := by
    rw [ restriction_compose_eq ];
    · grind;
    · linarith;
    · exact hp₂;
    · linarith;
  -- Apply the linearity of summation and the bounds from h_bound.
  have h_sum_bound : ∑ ρ₁, bernoulliRestrWeight p₁ ρ₁ * bernoulliRestrProb p₂ (fun ρ₂ => E (composeRestr ρ₁ ρ₂)) ≤ ∑ ρ₁, bernoulliRestrWeight p₁ ρ₁ * (if A ρ₁ then 1 else β) := by
    gcongr;
    · exact bernoulliRestrWeight_nonneg' _ hp₁.le hp₁_1 _;
    · split_ifs <;> [ exact bernoulliRestrProb_le_one' p₂ hp₂.le hp₂_1 _; exact h_bound _ ‹_› ];
  refine le_trans h_eq.le <| h_sum_bound.trans ?_;
  simp +decide [ Finset.sum_ite, bernoulliRestrProb ];
  rw [ ← Finset.sum_mul _ _ _ ];
  exact mul_le_of_le_one_left hβ ( le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_univ _ ) fun _ _ _ => bernoulliRestrWeight_nonneg' _ hp₁.le hp₁_1 _ ) ( by simp [ bernoulliRestrWeight_sum_one _ hp₁.le hp₁_1 ] ) )

/-! ## Helper: AND of functions with bounded dtDepth has nice CNF -/

/-
When each gate's restricted function has a width-l CNF representation,
    the AND of all gates also has a width-l CNF representation.
-/
lemma and_of_gates_has_cnf
    (s₂ : ℕ) (gates : Fin s₂ → DNF n) (l : ℕ) (ρ₁ : Restriction n)
    (h_gates : ∀ i : Fin s₂, dtDepth (restrictFn (gates i).eval ρ₁) ≤ l) :
    ∃ Ψ : CNF n, CNF.width Ψ ≤ l ∧
      (∀ c ∈ Ψ, c.Nodup) ∧
      (∀ c ∈ Ψ, ∀ l₁ ∈ c, ∀ l₂ ∈ c, l₁.var = l₂.var → l₁ = l₂) ∧
      (∀ x, CNF.eval Ψ x = (Finset.univ : Finset (Fin s₂)).val.toList.all
        (fun i => restrictFn (gates i).eval ρ₁ x)) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : CNF n, CNF.width Ψ ≤ l ∧ (∀ x, CNF.eval Ψ x = List.all (Finset.univ.val.toList.map (fun i => restrictFn (gates i).eval ρ₁)) (fun f => f x)) := by
    apply compression_and_of_cnfs;
    simp +zetaDelta at *;
    exact fun a => all_gates_have_small_cnf gates l ρ₁ h_gates a;
  -- Convert the CNF representation into a nice CNF representation using exists_nice �_c�nf_of_cnf.
  obtain ⟨Ψ', hΨ'⟩ : ∃ Ψ' : CNF n, CNF.width Ψ' ≤ CNF.width Ψ ∧ (∀ x, CNF.eval Ψ' x = CNF.eval Ψ x) ∧ (∀ c ∈ Ψ', c.Nodup) ∧ (∀ c ∈ Ψ', ∀ l₁ ∈ c, ∀ l₂ ∈ c, l₁.var = l₂.var → l₁ = l₂) := by
    apply exists_nice_cnf_of_cnf;
  exact ⟨ Ψ', le_trans hΨ'.1 hΨ.1, hΨ'.2.2.1, hΨ'.2.2.2, fun x => by simpa [ hΨ.2 ] using hΨ'.2.1 x ⟩

/-
When all gates have dtDepth ≤ l, the function f|_{ρ₁} (which equals the AND
    of restricted gates) has a nice width-l CNF.
-/
lemma depth3_restricted_has_nice_cnf
    (f : (Fin n → Bool) → Bool)
    (s₂ : ℕ) (gates : Fin s₂ → DNF n) (l : ℕ) (ρ₁ : Restriction n)
    (h_f : ∀ x, f x = true ↔ ∀ i : Fin s₂, (gates i).eval x = true)
    (h_gates : ∀ i : Fin s₂, dtDepth (restrictFn (gates i).eval ρ₁) ≤ l) :
    ∃ Ψ : CNF n, CNF.width Ψ ≤ l ∧
      (∀ c ∈ Ψ, c.Nodup) ∧
      (∀ c ∈ Ψ, ∀ l₁ ∈ c, ∀ l₂ ∈ c, l₁.var = l₂.var → l₁ = l₂) ∧
      (∀ x, CNF.eval Ψ x = restrictFn f ρ₁ x) := by
  -- Use the existence of from `and_of_g �ates�_has_cnf` and show that it satisfies the required properties.
  obtain ⟨Ψ, hΨ⟩ := and_of_gates_has_cnf s₂ gates l ρ₁ h_gates;
  use Ψ;
  simp_all +decide ;
  refine' ⟨ hΨ.2.2.1, fun x => _ ⟩;
  simp +decide [ restrictFn ];
  cases h : f ( ρ₁.extend x ) <;> simp_all +decide ;
  grind

/-
When ¬A(ρ₁) (all gates switched successfully), the second-stage
    switching bound applies.
-/
lemma depth3_second_stage_bound
    (f : (Fin n → Bool) → Bool)
    (s₂ : ℕ) (gates : Fin s₂ → DNF n) (l t : ℕ) (ρ₁ : Restriction n)
    (h_f : ∀ x, f x = true ↔ ∀ i : Fin s₂, (gates i).eval x = true)
    (h_gates : ∀ i : Fin s₂, dtDepth (restrictFn (gates i).eval ρ₁) ≤ l)
    (hl_pos : 0 < l) (hn : 0 < n)
    (p₂ : ℝ) (hp₂_pos : 0 < p₂) (hp₂_le : p₂ ≤ 1 / (40 * ↑l)) (hp₂_1 : p₂ ≤ 1) :
    bernoulliRestrProb p₂
      (fun ρ₂ => dtDepth (restrictFn f (composeRestr ρ₁ ρ₂)) > t) ≤
    (1 / 2 : ℝ) ^ t + Real.exp (-(↑n * p₂ / 3)) := by
  convert switching_bernoulli_dtDepth_cnf _ _ _ _ _ _ _ _ _ _ using 1;
  case convert_2 => exact ( Classical.choose ( depth3_restricted_has_nice_cnf f s₂ gates l ρ₁ h_f h_gates ) ) |> cleanCNF_D3;
  case convert_3 => exact l;
  any_goals assumption;
  · constructor <;> intro h;
    · convert switching_bernoulli_dtDepth_cnf _ _ _ _ _ _ _ _ _ _ using 1;
      exact l;
      any_goals assumption;
      · exact le_trans ( cleanCNF_D3_width_le _ ) ( Classical.choose_spec ( depth3_restricted_has_nice_cnf f s₂ gates l ρ₁ h_f h_gates ) |>.1 );
      · exact cleanCNF_D3_var_inj _
      · exact cleanCNF_D3_nodup _;
    · convert h hp₂_1 t using 1;
      have := Classical.choose_spec ( depth3_restricted_has_nice_cnf f s₂ gates l ρ₁ h_f h_gates );
      have h_eq : ∀ x, CNF.eval (cleanCNF_D3 (Classical.choose (depth3_restricted_has_nice_cnf f s₂ gates l ρ₁ h_f h_gates))) x = restrictFn f ρ₁ x := by
        exact fun x => by rw [ ← this.2.2.2 x, cleanCNF_D3_eval ] ;
      congr! 3;
      exact dtDepth_congr _ _ fun x => by rw [ restrictFn_composeRestr, restrictFn_congr _ _ _ h_eq ] ;
  · refine' le_trans _ ( Classical.choose_spec ( depth3_restricted_has_nice_cnf f s₂ gates l ρ₁ h_f h_gates ) |>.1 );
    exact cleanCNF_D3_width_le (Classical.choose (depth3_restricted_has_nice_cnf f s₂ gates l ρ₁ h_f h_gates));
  · exact Classical.choose_spec ( depth3_restricted_has_nice_cnf f s₂ gates l ρ₁ h_f h_gates ) |> fun h => cleanCNF_D3_var_inj _;
  · exact fun c hc => cleanCNF_D3_nodup _ _ hc

/-! ## Two-Stage Depth-3 Switching Bound -/

/-
**Depth-3 two-stage switching bound.**

    For a function f that is the AND of s₂ width-w DNF gates, under a composed
    Bernoulli(p₁ · p₂) restriction:

    `Pr[dtDepth(f|_ρ) > t] ≤ s₂ · ((1/2)^l + exp(-n·p₁/3)) + ((1/2)^t + exp(-n·p₂/3))`

    **Proof**: Decompose the composed restriction into two stages via
    `restriction_compose_eq`. At stage 1, the switching lemma + union bound give
    all gates becoming width-l CNFs with high probability. Compression yields a
    single width-l CNF for f|_{ρ₁}. At stage 2, the functional switching lemma
    bounds dtDepth of (f|_{ρ₁})|_{ρ₂} = f|_{ρ}.
-/
theorem depth3_switching_bound
    (f : (Fin n → Bool) → Bool)
    (s₂ : ℕ) (gates : Fin s₂ → DNF n) (w : ℕ) (l t : ℕ)
    -- f is the AND of the gates
    (h_f : ∀ x, f x = true ↔ ∀ i : Fin s₂, (gates i).eval x = true)
    -- Gate conditions for the switching lemma
    (hw : ∀ i, (gates i).width ≤ w) (hw_pos : 0 < w)
    (hnd : ∀ i, ∀ tm ∈ gates i, ∀ l₁ ∈ tm, ∀ l₂ ∈ tm, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ i, ∀ tm ∈ gates i, tm.Nodup)
    -- Restriction parameters
    (hn : 0 < n)
    (p₁ p₂ : ℝ)
    (hp₁_pos : 0 < p₁) (hp₁_le : p₁ ≤ 1 / (40 * ↑w)) (hp₁_1 : p₁ ≤ 1)
    (hp₂_pos : 0 < p₂) (hp₂_le : p₂ ≤ 1 / (40 * ↑l)) (hp₂_1 : p₂ ≤ 1)
    (hl_pos : 0 < l) :
    bernoulliRestrProb (p₁ * p₂)
      (fun ρ => dtDepth (restrictFn f ρ) > t) ≤
    ↑s₂ * ((1 / 2 : ℝ) ^ l + Real.exp (-(↑n * p₁ / 3))) +
    ((1 / 2 : ℝ) ^ t + Real.exp (-(↑n * p₂ / 3))) := by
  by_contra h_contra;
  -- Apply the two-stage bound with β = (1/2)^t + exp(-n*p₂/3).
  have h_two_stage : bernoulliRestrProb (p₁ * p₂) (fun ρ => dtDepth (restrictFn f ρ) > t) ≤ bernoulliRestrProb p₁ (fun ρ₁ => ∃ i : Fin s₂, dtDepth (restrictFn (gates i).eval ρ₁) > l) + ((1 / 2 : ℝ) ^ t + Real.exp (-(n * p₂ / 3))) := by
    apply two_stage_bound;
    all_goals norm_num [ hp₁_pos, hp₁_le, hp₁_1, hp₂_pos, hp₂_le, hp₂_1, hl_pos ];
    · positivity;
    · exact fun ρ₁ hρ₁ => depth3_second_stage_bound f s₂ gates l t ρ₁ h_f hρ₁ hl_pos hn p₂ hp₂_pos hp₂_le hp₂_1;
  refine h_contra <| h_two_stage.trans <| add_le_add ?_ le_rfl;
  convert switching_bernoulli_union_bound gates w l hw hw_pos hnd hnodup hn p₁ hp₁_pos hp₁_le hp₁_1 using 1

/-! ## Connecting to circuit_reduction_core for d = 3 -/

/-- **Depth-3 circuit switching lemma with composed restriction.**

    For a depth-3 circuit in normal form (AND of `s₂` width-`w` DNFs),
    under Bernoulli(`composedDelta w l 3`) = Bernoulli(`1/(40w) · 1/(40l)`),
    the probability that `dtDepth(f|_ρ) > t` is bounded by:

    `s₂ · ((1/2)^l + exp(−n·p₁/3)) + ((1/2)^t + exp(−n·p₂/3))`

    where `p₁ = 1/(40w)` and `p₂ = 1/(40l)`. This is the one-step
    depth-3 → depth-2 compression result: the switching lemma bound
    for reducing a depth-3 circuit to bounded decision-tree depth
    via a single composed random restriction.

    The exponential Chernoff tails `exp(−np/3)` vanish as `n → ∞`;
    the dominant terms `s₂ · (1/2)^l + (1/2)^t` give the switching
    lemma bound. See `circuit_reduction_depth3_le_eps` for the
    `≤ ε` corollary with specific parameter choices. -/
theorem circuit_reduction_depth3
    (f : (Fin n → Bool) → Bool)
    (s₂ : ℕ) (gates : Fin s₂ → DNF n) (w l t : ℕ)
    -- f is the AND of the gates
    (h_f : ∀ x, f x = true ↔ ∀ i : Fin s₂, (gates i).eval x = true)
    -- Gate conditions
    (hw : ∀ i, (gates i).width ≤ w) (hw_pos : 0 < w)
    (hnd : ∀ i, ∀ tm ∈ gates i, ∀ l₁ ∈ tm, ∀ l₂ ∈ tm, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ i, ∀ tm ∈ gates i, tm.Nodup)
    (hn : 0 < n) (hl_pos : 0 < l) :
    let p₁ : ℝ := 1 / (40 * ↑w)
    let p₂ : ℝ := 1 / (40 * ↑l)
    bernoulliRestrProb (composedDelta w (↑l) 3)
      (fun ρ => dtDepth (restrictFn f ρ) > t) ≤
    ↑s₂ * ((1 / 2 : ℝ) ^ l + Real.exp (-(↑n * p₁ / 3))) +
    ((1 / 2 : ℝ) ^ t + Real.exp (-(↑n * p₂ / 3))) := by
  -- composedDelta w (↑l) 3 = (1/(40w)) * (1/(40l)) since 3 - 2 = 1
  have h_delta : composedDelta w (↑l) 3 = (1 / (40 * ↑w)) * (1 / (40 * (↑l : ℝ))) := by
    unfold composedDelta; simp [pow_one]
  rw [h_delta]
  have hw_ge : (1 : ℝ) ≤ ↑w := Nat.one_le_cast.mpr hw_pos
  have hl_ge : (1 : ℝ) ≤ ↑l := Nat.one_le_cast.mpr hl_pos
  exact depth3_switching_bound f s₂ gates w l t h_f hw hw_pos hnd hnodup hn
    _ _ (by positivity) le_rfl
    (by rw [div_le_iff₀ (by positivity : (0:ℝ) < 40 * ↑w)]; nlinarith)
    (by positivity) le_rfl
    (by rw [div_le_iff₀ (by positivity : (0:ℝ) < 40 * ↑l)]; nlinarith)
    hl_pos

/-- **Depth-3 switching lemma, `≤ ε` version (asymptotic).**

    For a depth-3 circuit in normal form (AND of `s₂` width-`w` DNFs),
    choosing `l = ⌈logb 2 (2s₂/ε)⌉` and `t = ⌈logb 2 (2/ε)⌉`,
    the probability bound from `circuit_reduction_depth3` is at most
    `ε + s₂ · exp(−n/(120w)) + exp(−n/(120l))`.

    The exponential tails vanish as `n → ∞`, so the bound is `≤ ε`
    asymptotically. -/
theorem circuit_reduction_depth3_le_eps
    (f : (Fin n → Bool) → Bool)
    (s₂ : ℕ) (gates : Fin s₂ → DNF n) (w l t : ℕ)
    (h_f : ∀ x, f x = true ↔ ∀ i : Fin s₂, (gates i).eval x = true)
    (hw : ∀ i, (gates i).width ≤ w) (hw_pos : 0 < w)
    (hnd : ∀ i, ∀ tm ∈ gates i, ∀ l₁ ∈ tm, ∀ l₂ ∈ tm, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ i, ∀ tm ∈ gates i, tm.Nodup)
    (hn : 0 < n) (hl_pos : 0 < l)
    -- l and t are chosen so that the dominant terms sum to ≤ ε
    (ε : ℝ)
    (hl_bound : (s₂ : ℝ) * (1 / 2 : ℝ) ^ l ≤ ε / 2)
    (ht_bound : (1 / 2 : ℝ) ^ t ≤ ε / 2) :
    let p₁ : ℝ := 1 / (40 * ↑w)
    let p₂ : ℝ := 1 / (40 * ↑l)
    bernoulliRestrProb (composedDelta w (↑l) 3)
      (fun ρ => dtDepth (restrictFn f ρ) > t) ≤
    ε + ↑s₂ * Real.exp (-(↑n * p₁ / 3)) + Real.exp (-(↑n * p₂ / 3)) := by
  have h := circuit_reduction_depth3 f s₂ gates w l t h_f hw hw_pos hnd hnodup hn hl_pos
  simp only at h ⊢
  linarith

end LMN
end