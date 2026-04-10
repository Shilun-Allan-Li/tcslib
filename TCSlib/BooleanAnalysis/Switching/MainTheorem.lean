import TCSlib.BooleanAnalysis.Switching.RoundTrip

/-!
# Switching Lemma — Main Theorem

The main switching lemma statement, counting bounds, combinatorial inequalities,
and the corollary converting to CNF representation.
-/

open Classical

namespace SwitchingLemma2

variable {n : ℕ}

/-! ### Counting bounds -/

/-- Each aux data entry is `(position, direction)` with at most `(2w)^d` fibers. -/
private lemma fiber_bound {n : ℕ} (f : DNF n) (w s d : ℕ)
    (hw : f.width ≤ w) (hd : d ≤ s) (γ : Restriction n) :
    (Finset.univ.filter fun ρ : Restriction n =>
        IsRestriction s ρ ∧ IsBadRestriction f.eval d ρ ∧
        (razborovEncode f w d ρ).1 = γ).card ≤ (2 * w) ^ d := by
  sorry

/-- **Razborov counting bound**. -/
private lemma bad_count_bound {n : ℕ} (f : DNF n) (w s d : ℕ)
    (hw : f.width ≤ w) (hd : d ≤ s) :
    (Finset.univ.filter fun ρ : Restriction n =>
        IsRestriction s ρ ∧ IsBadRestriction f.eval d ρ).card ≤
    n.choose (s - d) * 2 ^ (n - (s - d)) * (2 * w) ^ d := by
  sorry

/-! ## Combinatorial inequalities -/

private lemma bad_filter_empty_of_d_ge_s {n : ℕ} (f : DNF n) (d s : ℕ) (hds : s ≤ d) :
    (Finset.univ.filter fun ρ : Restriction n =>
        IsRestriction s ρ ∧ IsBadRestriction f.eval d ρ) = ∅ := by
  simp +zetaDelta at *
  exact fun ρ hρ => not_lt.mpr (le_trans (dtDepth_restrictFn_le_numFree _ _)
    (by linarith [hρ.symm]))

private lemma choose_mul_pow_bound {n s d : ℕ} (hs : 5 * s ≤ n) (hd : d ≤ s) :
    n.choose (s - d) * (2 * n) ^ d ≤ n.choose s * (5 * s) ^ d := by
  induction d with
  | zero => norm_num
  | succ d hd_ih =>
    have h_simp : (Nat.choose n (s - d - 1)) * (2 * n) ≤ (Nat.choose n (s - d)) * (5 * s) := by
      set m := s - d - 1 with hm_def
      have hm_succ : s - d = m + 1 := by omega
      rw [hm_succ]
      have h_eq := Nat.choose_succ_right_eq n m
      have h_mn : m ≤ n := by omega
      have h_pos : 0 < Nat.choose n m := Nat.choose_pos h_mn
      have h_sub_add : (n - m) + m = n := Nat.sub_add_cancel h_mn
      suffices h : 2 * n * (m + 1) ≤ (n - m) * (5 * s) by nlinarith [h_eq]
      have hms : m + 1 + d = s := by omega
      zify [h_mn] at h_sub_add hs ⊢
      nlinarith [hms]
    have := hd_ih ( Nat.le_of_succ_le hd )
    rw [ Nat.sub_sub ] at *
    rw [ pow_succ', pow_succ' ]
    nlinarith [ pow_pos ( show 0 < 2 * n by linarith ) d ]

/-! ## Main theorem -/

theorem switching_lemma {n : ℕ} (hn : 0 < n) (f : DNF n) (w s d : ℕ)
    (hw : f.width ≤ w) (hs : 5 * s ≤ n) :
    (Finset.univ.filter fun ρ : Restriction n =>
        IsRestriction s ρ ∧ IsBadRestriction f.eval d ρ).card * n ^ d ≤
    numSRestrictions n s * (10 * s * w) ^ d := by
  by_cases hds : d ≤ s
  · refine le_trans (Nat.mul_le_mul_right _ (bad_count_bound f w s d hw hds)) ?_
    convert Nat.mul_le_mul_right _ (choose_mul_pow_bound hs hds) |> le_trans <| ?_ using 1; ring
    rotate_left
    exact 2 ^ (n - s) * (2 * w) ^ d
    · unfold numSRestrictions; ring_nf
      norm_num [mul_assoc, mul_left_comm, ← mul_pow]
      ring_nf; norm_num [mul_assoc, mul_comm, mul_left_comm]
    · rw [show n - (s - d) = n - s + d by omega]; ring
  · rw [bad_filter_empty_of_d_ge_s f d s (by linarith)]; norm_num

/-! ## Decision tree to DNF/CNF conversion -/

private def toDNF {n : ℕ} : DecisionTree n → DNF n
  | .leaf true  => [[]   ]
  | .leaf false => []
  | .branch v lo hi =>
    ((toDNF lo).map fun t => ⟨v, true⟩ :: t) ++
    ((toDNF hi).map fun t => ⟨v, false⟩ :: t)

private def toCNF {n : ℕ} : DecisionTree n → CNF n
  | .leaf true  => []
  | .leaf false => [[]   ]
  | .branch v lo hi =>
    ((toCNF lo).map fun c => ⟨v, false⟩ :: c) ++
    ((toCNF hi).map fun c => ⟨v, true⟩ :: c)

private lemma dtDepth_witness {n : ℕ} (f : (Fin n → Bool) → Bool) :
    ∃ T : DecisionTree n, T.depth ≤ dtDepth f ∧ ∀ x, T.eval x = f x := by
  classical
  let p := fun d => ∃ T : DecisionTree n, T.depth ≤ d ∧ ∀ x, T.eval x = f x
  have hexists : ∃ d, p d := ⟨n, buildFullDTree f 0 (fun _ => false),
    buildFullDTree_depth f 0 (Nat.zero_le n) _,
    fun x => buildFullDTree_eval f 0 (Nat.zero_le n) _ x (fun _ hi => by omega)⟩
  have hspec := Nat.find_spec hexists
  show p (dtDepth f)
  unfold dtDepth
  convert hspec using 1

lemma dtDepth_le_implies_small_dnf_cnf {n : ℕ} (f : (Fin n → Bool) → Bool) (d : ℕ)
    (h : dtDepth f ≤ d) :
    (∃ φ : DNF n, φ.width ≤ d ∧ ∀ x, φ.eval x = f x) ∧
    (∃ ψ : CNF n, ψ.width ≤ d ∧ ∀ x, ψ.eval x = f x) := by
  obtain ⟨T, hTd, hTeval⟩ := dtDepth_witness f
  have hTd' : T.depth ≤ d := le_trans hTd h
  constructor
  · use SwitchingLemma2.toDNF T, by
      have h_width_le_depth : ∀ T : DecisionTree n, (toDNF T).width ≤ T.depth := by
        intro T;
        have h_width_induction : ∀ T : DecisionTree n, ∀ t ∈ toDNF T, t.length ≤ T.depth := by
          intro T
          induction' T with v lo hi hlo hhi;
          · cases v <;> simp +decide [ toDNF ];
          · intro t ht; unfold toDNF at ht; simp_all +decide [ DecisionTree.depth ] ;
            grind;
        have h_width_induction : ∀ {l : List ℕ}, (∀ x ∈ l, x ≤ T.depth) → List.foldr max 0 l ≤ T.depth := by
          intros l hl; induction l <;> aesop;
        exact h_width_induction fun x hx => by aesop;
      exact le_trans ( h_width_le_depth T ) hTd', by
      intro x;
      convert hTeval x using 1;
      clear hTd hTeval hTd' h;
      induction' T with v lo hi ihlo ihhi;
      · cases v <;> simp +decide [ toDNF ];
        · rfl;
        · rfl;
      · unfold DNF.eval at *; simp_all +decide [ DecisionTree.eval ] ;
        unfold toDNF; simp +decide [ *, List.any_append ] ;
        split_ifs <;> simp_all +decide [ Function.comp, Term.eval ];
        · simp_all +decide [ Function.comp, Literal.eval ];
          simp_all +decide [ Function.comp, List.any_eq, List.all_eq ];
        · simp_all +decide [ Function.comp, List.any_eq, Literal.eval ]
  · use toCNF T;
    refine' ⟨ le_trans _ hTd', fun x => _ ⟩;
    · have h_clause_length : ∀ T : DecisionTree n, ∀ c ∈ toCNF T, c.length ≤ T.depth := by
        intro T c hc
        induction' T with v lo hi ih_lo ih_hi generalizing c;
        · cases v <;> cases hc ; trivial;
          contradiction;
        · have h_clauses : ∀ c ∈ toCNF (DecisionTree.branch lo hi ih_lo), ∃ c' ∈ toCNF hi ∪ toCNF ih_lo, c = ⟨lo, false⟩ :: c' ∨ c = ⟨lo, true⟩ :: c' := by
            intro c hc; rw [ show toCNF ( DecisionTree.branch lo hi ih_lo ) = ( toCNF hi |> List.map fun c' => ⟨ lo, false ⟩ :: c' ) ++ ( toCNF ih_lo |> List.map fun c' => ⟨ lo, true ⟩ :: c' ) from rfl ] at hc; aesop;
          obtain ⟨ c', hc', rfl | rfl ⟩ := h_clauses c hc <;> simp +arith +decide [ *, DecisionTree.depth ];
          · grind;
          · grind;
      have h_foldr_le : ∀ {l : List ℕ}, (∀ x ∈ l, x ≤ T.depth) → List.foldr Max.max 0 l ≤ T.depth := by
        intros l hl; induction l <;> aesop;
      exact h_foldr_le fun x hx => by aesop;
    · rw [ ← hTeval, eq_comm ];
      have h_equiv : ∀ T : DecisionTree n, ∀ x : Fin n → Bool, T.eval x = (toCNF T).eval x := by
        intros T x; induction' T with v lo hi ih_lo ih_hi generalizing x; simp +decide [ *, CNF.eval ] ;
        · cases v <;> simp +decide [ DecisionTree.eval ];
          · exact ⟨ [ ], by tauto, by tauto ⟩;
          · exact fun t ht => by cases ht;
        · simp +decide [ *, DecisionTree.eval, CNF.eval ];
          rw [ show toCNF ( DecisionTree.branch lo hi ih_lo ) = ( toCNF hi |> List.map fun c => ⟨ lo, false ⟩ :: c ) ++ ( toCNF ih_lo |> List.map fun c => ⟨ lo, true ⟩ :: c ) by rfl ];
          split_ifs <;> simp_all +decide [ CNF.evalClause ];
          · simp +decide [ *, Function.comp, Literal.eval ];
            grind +splitIndPred;
          · simp +decide [ *, Function.comp, Literal.eval ];
            grind;
      exact h_equiv T x

theorem switching_corollary {n : ℕ} (hn : 0 < n) (f : DNF n) (w s : ℕ)
    (hw : f.width ≤ w) (hs : 5 * s ≤ n) :
    (Finset.univ.filter fun ρ : Restriction n =>
        IsRestriction s ρ ∧
        ¬ ∃ ψ : CNF n, ψ.width ≤ w ∧
          ∀ x, ψ.eval x = restrictFn f.eval ρ x).card * n ^ w ≤
    numSRestrictions n s * (10 * s * w) ^ w := by
  apply le_trans _ (switching_lemma hn f w s w hw hs)
  apply Nat.mul_le_mul_right
  apply Finset.card_le_card
  intro ρ hρ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
  refine ⟨hρ.1, ?_⟩
  show dtDepth (restrictFn f.eval ρ) > w
  by_contra hgood; push_neg at hgood
  exact hρ.2 (dtDepth_le_implies_small_dnf_cnf _ w hgood).2

end SwitchingLemma2
