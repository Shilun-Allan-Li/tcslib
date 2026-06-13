import TCSlib.BooleanAnalysis.LMN.NormalFormConversion
import TCSlib.BooleanAnalysis.LMN.SwitchingBernoulli
import Mathlib

/-!
# Circuit Helper Lemmas for LMN

Helper lemmas for proving switching lemma bounds for depth-2 circuits.
-/

open BoolCircuit SwitchingLemma2 SwitchingBernoulli
open Classical in
attribute [local instance] Classical.propDecidable
noncomputable section

namespace LMN

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ## Function extensionality for restrictions -/

lemma restrictFn_ext' {f g : (Fin n → Bool) → Bool} (h : ∀ x, f x = g x)
    (ρ : Restriction n) : restrictFn f ρ = restrictFn g ρ := by
  ext x; simp [restrictFn]; exact h _

lemma bernoulliRestrProb_congr_fn {f g : (Fin n → Bool) → Bool}
    (h : ∀ x, f x = g x) (p : ℝ) (t : ℕ) :
    bernoulliRestrProb p (fun ρ => dtDepth (restrictFn f ρ) > t) =
    bernoulliRestrProb p (fun ρ => dtDepth (restrictFn g ρ) > t) := by
  congr 1; ext ρ; rw [restrictFn_ext' h]

/-! ## De-duplication of terms by variable -/

/-- Remove literals whose variable already appeared earlier. -/
def dedupTermVar (t : Term n) : Term n :=
  t.foldr (fun l acc =>
    if acc.any (fun l' => decide (l'.var = l.var)) then acc
    else l :: acc) []

/-- Check if a term has contradictory literals. -/
def termHasContradiction (t : Term n) : Bool :=
  t.any (fun l₁ => t.any (fun l₂ => decide (l₁.var = l₂.var) && decide (l₁.neg ≠ l₂.neg)))

/-- Clean a DNF: first remove contradictory terms, then de-duplicate each term. -/
def cleanDNF (d : DNF n) : DNF n :=
  (d.filter (fun t => !termHasContradiction t)).map dedupTermVar

/-- Clean a CNF: first remove tautological clauses, then de-duplicate each clause. -/
def cleanCNF (c : CNF n) : CNF n :=
  (c.filter (fun t => !termHasContradiction t)).map dedupTermVar

/-! ## Properties of de-duplication -/

lemma dedupTermVar_nodup (t : Term n) : (dedupTermVar t).Nodup := by
  -- By induction on the list t, we can show that the foldr operation preserves the nodup property.
  have h_ind : ∀ (t : List (Literal n)) (acc : List (Literal n)), List.Nodup acc → List.Nodup (t.foldr (fun l acc => if acc.any (fun l' => decide (l'.var = l.var)) then acc else l :: acc) acc) := by
    intro t acc hacc; induction t <;> aesop;
  exact h_ind _ _ ( by simp +decide )

lemma dedupTermVar_var_inj (t : Term n) :
    ∀ l₁ ∈ dedupTermVar t, ∀ l₂ ∈ dedupTermVar t, l₁.var = l₂.var → l₁ = l₂ := by
      have h_ind : ∀ (t : List (Literal n)) (acc : List (Literal n)), acc.Nodup → (∀ l₁ ∈ acc, ∀ l₂ ∈ acc, l₁.var = l₂.var → l₁ = l₂) → ∀ l₁ ∈ List.foldr (fun l acc => if acc.any (fun l' => decide (l'.var = l.var)) then acc else l :: acc) acc t, ∀ l₂ ∈ List.foldr (fun l acc => if acc.any (fun l' => decide (l'.var = l.var)) then acc else l :: acc) acc t, l₁.var = l₂.var → l₁ = l₂ := by
        intros t acc hacc hvar_inj
        induction' t with l t ih generalizing acc;
        · exact hvar_inj;
        · grind;
      exact h_ind _ _ ( by simp +decide [ List.nodup_nil ] ) ( by simp +decide [ List.nodup_nil ] )

lemma dedupTermVar_width_le (t : Term n) :
    (dedupTermVar t).length ≤ t.length := by
      -- By induction on the list t, we can show that the length of the deduplicated list is less than or equal to the original list length.
      have dedupTermVar_length_le_induction (t : Term n) (acc : Term n) : List.length (List.foldr (fun l acc => if List.any acc (fun l' => decide (l'.var = l.var)) then acc else l :: acc) acc t) ≤ List.length t + List.length acc := by
        induction' t with t_head t_tail ih generalizing acc;
        · simp +arith +decide;
        · grind;
      convert dedupTermVar_length_le_induction t [] using 1

/-
A contradictory term always evaluates to false under AND (term evaluation).
-/
lemma contradiction_term_eval_false (t : Term n) (x : Fin n → Bool)
    (hc : termHasContradiction t = true) :
    Term.eval t x = false := by
      -- By definition of termHasContradiction, there exist l₁ and l₂ in t such that l₁.var = l₂.var and l₁.neg ≠ l₂.neg.
      obtain ⟨l₁, l₂, hl₁, hl₂, h_var, h_neg⟩ : ∃ l₁ l₂ : Literal n, l₁ ∈ t ∧ l₂ ∈ t ∧ l₁.var = l₂.var ∧ l₁.neg ≠ l₂.neg := by
        unfold termHasContradiction at hc;
        grind;
      unfold Term.eval;
      cases h : l₁.neg <;> cases h' : l₂.neg <;> simp_all +decide [ Literal.eval ]; all_goals grind

/-
De-duplication of a non-contradictory term preserves AND evaluation.
-/
lemma dedupTermVar_preserves_term_eval (t : Term n) (x : Fin n → Bool)
    (hnc : termHasContradiction t = false) :
    Term.eval (dedupTermVar t) x = Term.eval t x := by
      unfold termHasContradiction at hnc;
      induction' t with l t ih;
      · rfl;
      · by_cases h : ∃ l' ∈ t, l'.var = l.var <;> simp_all +decide [ dedupTermVar ];
        · split_ifs <;> simp_all +decide [ Term.eval ];
          · obtain ⟨ l', hl', hl'' ⟩ := h; specialize hnc; have := hnc.1 l' hl' hl''.symm; simp_all +decide [ Literal.eval ] ;
            grind;
          · grind;
        · rw [ if_neg ];
          · simp_all +decide [ Term.eval ];
            rw [ ih hnc ];
          · contrapose! h;
            obtain ⟨ x, hx₁, hx₂ ⟩ := h;
            have h_foldr : ∀ (l : List (Literal n)), ∀ x ∈ List.foldr (fun l acc => if ∃ x ∈ acc, x.var = l.var then acc else l :: acc) [] l, x ∈ l := by
              intro l x hx; induction l <;> aesop;
            exact ⟨ x, h_foldr t x hx₁, hx₂ ⟩

/-
cleanDNF preserves DNF evaluation.
-/
lemma cleanDNF_eval (d : DNF n) (x : Fin n → Bool) :
    (cleanDNF d).eval x = d.eval x := by
      unfold DNF.eval cleanDNF;
      induction' d with t d ih;
      · rfl;
      · by_cases h : termHasContradiction t <;> simp_all +decide [ dedupTermVar_preserves_term_eval ];
        exact fun h' => absurd h' ( by rw [ contradiction_term_eval_false t x h ] ; decide )

/-
A contradictory clause always evaluates to true under OR (CNF.evalClause).
-/
lemma contradiction_clause_eval_true (t : Term n) (x : Fin n → Bool)
    (hc : termHasContradiction t = true) :
    CNF.evalClause t x = true := by
      unfold termHasContradiction at hc;
      unfold CNF.evalClause;
      simp_all +decide [ Literal.eval ];
      grind

/-
De-duplication of a non-contradictory clause preserves OR evaluation.
-/
lemma dedupTermVar_preserves_clause_eval (t : Term n) (x : Fin n → Bool)
    (hnc : termHasContradiction t = false) :
    CNF.evalClause (dedupTermVar t) x = CNF.evalClause t x := by
      induction' t with l t ih generalizing x;
      · rfl;
      · by_cases h : (dedupTermVar t).any (fun l' => l'.var = l.var) <;> simp_all +decide [ dedupTermVar ];
        · obtain ⟨ y, hy₁, hy₂ ⟩ := h;
          have h_eval_eq : l.eval x = y.eval x := by
            unfold termHasContradiction at hnc; simp_all +decide [ List.any ] ;
            have h_eval_eq : ∀ {l : Literal n} {t : List (Literal n)}, l ∈ List.foldr (fun l acc => if ∃ x ∈ acc, x.var = l.var then acc else l :: acc) [] t → l ∈ t := by
              intros l t hl; induction t <;> aesop;
            unfold Literal.eval; aesop;
          unfold CNF.evalClause at *; simp_all +decide [ List.any_cons ] ;
          rw [ ← ih x ];
          · grind;
          · unfold termHasContradiction at *; simp_all +decide [ List.any_cons ] ;
            exact fun x hx y hy hxy => hnc.2 x hx |>.2 y hy hxy;
        · simp_all +decide [ termHasContradiction, List.foldr ];
          split_ifs <;> simp_all +decide [ CNF.evalClause ];
          · tauto;
          · rw [ ih x fun x hx y hy hxy => hnc.2 x hx |>.2 y hy hxy ]

/-
cleanCNF preserves CNF evaluation.
-/
lemma cleanCNF_eval (c : CNF n) (x : Fin n → Bool) :
    CNF.eval (cleanCNF c) x = CNF.eval c x := by
      unfold cleanCNF CNF.eval;
      induction' c with t c ih <;> simp +decide [ * ];
      by_cases h : termHasContradiction t <;> simp +decide [ h, contradiction_clause_eval_true, dedupTermVar_preserves_clause_eval ];
      · grind
      · grind

/-
cleanDNF has width ≤ original width.
-/
lemma cleanDNF_width_le (d : DNF n) :
    (cleanDNF d).width ≤ d.width := by
      simp_all +decide [ cleanDNF, DNF.width ];
      have h_foldr_max_le : ∀ {l1 l2 : List ℕ}, (∀ x ∈ l1, x ≤ List.foldr max 0 l2) → List.foldr max 0 l1 ≤ List.foldr max 0 l2 := by
        intros l1 l2 h; induction l1 <;> aesop;
      apply h_foldr_max_le;
      intro x hx
      obtain ⟨t, ht⟩ : ∃ t ∈ d, x = Term.width (dedupTermVar t) ∧ !termHasContradiction t := by
        grind;
      have h_foldr_max_le : ∀ {l : List ℕ}, t.width ∈ l → List.foldr max 0 l ≥ t.width := by
        intros l hl; induction l <;> aesop;
      exact ht.2.1.symm ▸ le_trans ( dedupTermVar_width_le t ) ( h_foldr_max_le ( List.mem_map.mpr ⟨ t, ht.1, rfl ⟩ ) )

/-
cleanCNF has width ≤ original width.
-/
lemma cleanCNF_width_le (c : CNF n) :
    (cleanCNF c).width ≤ c.width := by
      have h_max_le : ∀ {s t : ℕ}, s ≤ t → ∀ {a : ℕ}, a ≤ s → a ≤ t := by
        exact fun h a ha => le_trans ha h;
      contrapose! h_max_le;
      exact absurd h_max_le ( not_lt_of_ge ( by
        have h_foldr_le : ∀ (l : List (Term n)), (l.map (fun t => Term.width (dedupTermVar t))).foldr max 0 ≤ (l.map Term.width).foldr max 0 := by
          intro l
          induction' l with t l ih;
          · rfl;
          · exact max_le_max ( dedupTermVar_width_le t ) ih;
        convert h_foldr_le ( List.filter ( fun t => !termHasContradiction t ) c ) |> le_trans <| ?_ using 1;
        · unfold cleanCNF;
          unfold CNF.width; aesop;
        · have h_foldr_le : ∀ (l : List (Term n)), (l.map Term.width).foldr max 0 ≥ ((l.filter (fun t => !termHasContradiction t)).map Term.width).foldr max 0 := by
            intro l; induction l <;> simp +decide [ * ] ;
            grind;
          exact h_foldr_le c ) )

/-
cleanDNF satisfies var_inj.
-/
lemma cleanDNF_var_inj (d : DNF n) :
    ∀ t ∈ cleanDNF d, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂ := by
      intro t ht l₁ hl₁ l₂ hl₂ hvar
      have h_l1_l2 : ∃ t' ∈ d, t = dedupTermVar t' := by
        unfold cleanDNF at ht; aesop;
      obtain ⟨t', ht', rfl⟩ := h_l1_l2
      exact dedupTermVar_var_inj t' l₁ hl₁ l₂ hl₂ hvar

/-
cleanDNF satisfies Nodup.
-/
lemma cleanDNF_nodup (d : DNF n) :
    ∀ t ∈ cleanDNF d, t.Nodup := by
      intro t ht
      rw [cleanDNF] at ht
      rcases List.mem_map.mp ht with ⟨t₀, ht₀, rfl⟩
      apply dedupTermVar_nodup

/-
cleanCNF satisfies var_inj.
-/
lemma cleanCNF_var_inj (c : CNF n) :
    ∀ t ∈ cleanCNF c, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂ := by
      unfold cleanCNF;
      intro t ht l₁ hl₁ l₂ hl₂ hvar
      rcases List.mem_map.mp ht with ⟨t₀, -, rfl⟩
      exact dedupTermVar_var_inj t₀ l₁ hl₁ l₂ hl₂ hvar

/-
cleanCNF satisfies Nodup.
-/
lemma cleanCNF_nodup (c : CNF n) :
    ∀ t ∈ cleanCNF c, t.Nodup := by
      unfold cleanCNF;
      intro t ht
      rcases List.mem_map.mp ht with ⟨t₀, -, rfl⟩
      exact dedupTermVar_nodup t₀

/-! ## General switching lemma (without var_inj/Nodup requirements) -/

theorem switching_bernoulli_dtDepth_dnf_general (f : DNF n) (w : ℕ)
    (hw : f.width ≤ w) (hw_pos : 0 < w)
    (hn : 0 < n) (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1 / (40 * ↑w)) (hp1 : p ≤ 1)
    (t : ℕ) :
    bernoulliRestrProb p (fun ρ => dtDepth (restrictFn f.eval ρ) > t) ≤
    (1 / 2 : ℝ) ^ t + Real.exp (-(↑n * p / 3)) := by
  have h_eq : ∀ x, (cleanDNF f).eval x = f.eval x := cleanDNF_eval f
  rw [show f.eval = (cleanDNF f).eval from funext (fun x => (h_eq x).symm)]
  exact switching_bernoulli_dtDepth_dnf (cleanDNF f) w
    (le_trans (cleanDNF_width_le f) hw) hw_pos
    (cleanDNF_var_inj f) (cleanDNF_nodup f)
    hn p hp_pos hp_le hp1 t

theorem switching_bernoulli_dtDepth_cnf_general (f : CNF n) (w : ℕ)
    (hw : CNF.width f ≤ w) (hw_pos : 0 < w)
    (hn : 0 < n) (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1 / (40 * ↑w)) (hp1 : p ≤ 1)
    (t : ℕ) :
    bernoulliRestrProb p (fun ρ => dtDepth (restrictFn (CNF.eval f) ρ) > t) ≤
    (1 / 2 : ℝ) ^ t + Real.exp (-(↑n * p / 3)) := by
  have h_eq : ∀ x, CNF.eval (cleanCNF f) x = CNF.eval f x := cleanCNF_eval f
  rw [show CNF.eval f = CNF.eval (cleanCNF f) from funext (fun x => (h_eq x).symm)]
  exact switching_bernoulli_dtDepth_cnf (cleanCNF f) w
    (le_trans (cleanCNF_width_le f) hw) hw_pos
    (cleanCNF_var_inj f) (cleanCNF_nodup f)
    hn p hp_pos hp_le hp1 t

/-! ## Depth constraints -/

lemma depth_le_one_children_are_lits (cs : List (Circuit n)) (isAnd : Bool)
    (hd : (Circuit.node isAnd cs).depth ≤ 1) :
    ∀ c ∈ cs, ∃ l : Lit n, c = .lit l := by
      intro c hc;
      have h_c_depth_zero : c.depth = 0 := by
        have h_foldr : ∀ {l : List (Circuit n)}, c ∈ l → l.foldr (fun c acc => max c.depth acc) 0 ≥ c.depth := by
          intros l hl; induction l <;> aesop;
        exact le_antisymm ( Nat.le_of_not_lt fun h => by have := h_foldr hc; exact absurd hd ( by unfold Circuit.depth; norm_num; linarith ) ) ( Nat.zero_le _ );
      rcases c with ( _ | ⟨ isAnd, cs ⟩ ) <;> simp_all +decide [ Circuit.depth ]

lemma depth_le_two_children_depth_le_one (cs : List (Circuit n)) (isAnd : Bool)
    (hd : (Circuit.node isAnd cs).depth ≤ 2) :
    ∀ c ∈ cs, c.depth ≤ 1 := by
      induction' cs with c cs ih <;> simp_all +arith +decide [ Circuit.depth ]

/-! ## Depth-2 circuit to DNF/CNF -/

/-- Convert a depth-≤-1 AND-subcircuit to a term: AND of its literal children. -/
def depth1AndToTerm (c : Circuit n) : Term n :=
  match c with
  | .lit l => [l.toLiteral]
  | .node _ cs => cs.filterMap (fun c' =>
      match c' with
      | .lit l => some l.toLiteral
      | _ => none)

/-- Convert a depth-≤-2 OR-top circuit to a DNF. -/
def depth2OrToDNF (cs : List (Circuit n)) : DNF n :=
  cs.flatMap (fun c =>
    match c with
    | .lit l => [[l.toLiteral]]
    | .node true cs' => [cs'.filterMap (fun c' =>
        match c' with
        | .lit l => some l.toLiteral
        | _ => none)]
    | .node false cs' => cs'.filterMap (fun c' =>
        match c' with
        | .lit l => some [l.toLiteral]
        | _ => none))

/-- Convert a depth-≤-2 AND-top circuit to a CNF. -/
def depth2AndToCNF (cs : List (Circuit n)) : CNF n :=
  cs.flatMap (fun c =>
    match c with
    | .lit l => [[l.toLiteral]]
    | .node false cs' => [cs'.filterMap (fun c' =>
        match c' with
        | .lit l => some l.toLiteral
        | _ => none)]
    | .node true cs' => cs'.filterMap (fun c' =>
        match c' with
        | .lit l => some [l.toLiteral]
        | _ => none))

/-
depth2OrToDNF preserves evaluation for depth-≤-2 OR-circuits.
-/
lemma depth2OrToDNF_eval (cs : List (Circuit n))
    (hd : (Circuit.node false cs).depth ≤ 2)
    (x : Fin n → Bool) :
    (depth2OrToDNF cs).eval x = (Circuit.node false cs).eval x := by
      -- For each child c with depth ≤ 1 (by depth_le_two_children_depth_le_one):
      -- - c = lit l: subcircuitToDNFContrib = [[l.toLiteral]], eval = l.eval x. DNF.eval of this = l.toLiteral.eval x = l.eval x (by Lit.eval_eq_toLiteral_eval).
      -- - c = node true cs': children of cs' are all lits (by depth_le_one_children_are_lits). subcircuitToDNFContrib returns [cs'.filterMap ...]. Since all children are lits, filterMap returns all their toLiterals. This term's eval = all literals evaluate to true = AND of lits = c.eval x.
      have h_child_eval (c : Circuit n) (hc : c ∈ cs) : (depth2OrToDNF [c]).eval x = c.eval x := by
        rcases c with ( _ | ⟨ l ⟩ | ⟨ isAnd, cs ⟩ );
        · unfold depth2OrToDNF; simp +decide [ BoolCircuit.Lit.eval_eq_toLiteral_eval ] ;
          unfold DNF.eval; simp +decide [ Circuit.eval ] ;
          unfold Term.eval; simp +decide [ Lit.toLiteral ] ;
          unfold Literal.eval; aesop;
        · have h_lits : ∀ c' ∈ ‹List (Circuit n)›, ∃ l : Lit n, c' = .lit l := by
            apply depth_le_one_children_are_lits;
            exact depth_le_two_children_depth_le_one cs false hd _ hc;
          unfold depth2OrToDNF Circuit.eval; simp +decide [ h_lits ] ;
          have h_lits : ∀ {l : List (Circuit n)}, (∀ c' ∈ l, ∃ l : Lit n, c' = .lit l) → DNF.eval (List.filterMap (fun c' => match c' with | .lit l => some [l.toLiteral] | _ => none) l) x = List.foldr (fun c acc => c.eval x || acc) false l := by
            intro l hl; induction l <;> simp_all +decide [ DNF.eval ] ;
            rcases hl.1 with ⟨ l, rfl ⟩ ; simp +decide [ Circuit.eval ] ;
            unfold Term.eval; simp +decide [ Lit.eval ] ;
            unfold Literal.eval; simp +decide [ Lit.toLiteral ] ;
            cases l.sign <;> simp +decide [ * ];
          exact h_lits ‹_›;
        · unfold depth2OrToDNF;
          unfold DNF.eval Circuit.eval; simp +decide [ List.flatMap ] ;
          rename_i l;
          have h_lits : ∀ c ∈ l, ∃ l' : Lit n, c = .lit l' := by
            apply depth_le_one_children_are_lits;
            exact depth_le_two_children_depth_le_one cs false hd _ hc;
          have h_lits : ∀ {l : List (Circuit n)}, (∀ c ∈ l, ∃ l' : Lit n, c = .lit l') → Term.eval (List.filterMap (fun c' => match c' with | .lit l => some l.toLiteral | _ => none) l) x = List.foldr (fun c acc => c.eval x && acc) true l := by
            intros l hl; induction' l with c l ih <;> simp_all +decide [ Term.eval ] ;
            rcases hl.1 with ⟨ l', rfl ⟩ ; simp +decide [ Circuit.eval ];
            unfold Literal.eval; simp +decide [ Lit.toLiteral ] ;
            cases l'.sign <;> simp +decide [ * ];
          exact h_lits ‹_›;
      -- By definition of `depth2OrToDNF`, we can rewrite the left-hand side of the equation.
      have h_depth2OrToDNF : depth2OrToDNF cs = cs.flatMap (fun c => depth2OrToDNF [c]) := by
        unfold depth2OrToDNF; aesop;
      simp_all +decide [ DNF.eval, Circuit.eval ];
      have h_foldr : ∀ (cs : List (Circuit n)), List.foldr (fun c acc => c.eval x || acc) false cs = decide (∃ c ∈ cs, c.eval x = true) := by
        intro cs; induction cs <;> aesop;
      grind

/-
depth2AndToCNF preserves evaluation for depth-≤-2 AND-circuits.
-/
lemma depth2AndToCNF_eval (cs : List (Circuit n))
    (hd : (Circuit.node true cs).depth ≤ 2)
    (x : Fin n → Bool) :
    CNF.eval (depth2AndToCNF cs) x = (Circuit.node true cs).eval x := by
      -- Prove that for any child c ∈ cs with c.depth ≤ 1, the translation works.
      have h_child (c : Circuit n) (hc : c ∈ cs) (hc_depth : c.depth ≤ 1) :
        CNF.eval (depth2AndToCNF [c]) x = c.eval x := by
          rcases c with ( _ | ⟨ l ⟩ | ⟨ isAnd, cs ⟩ ) <;> simp_all +decide [ Circuit.depth ];
          · unfold depth2AndToCNF; simp +decide [ Circuit.eval ] ;
            unfold CNF.eval; simp +decide [ CNF.evalClause, Literal.eval ] ;
            unfold Lit.toLiteral; aesop;
          · -- Since the depth of the node is 0, all its children must be literals.
            have h_children_literals : ∀ c ∈ (‹List (Circuit n)›), ∃ l : Lit n, c = .lit l := by
              have h_children_literals : ∀ c ∈ (‹List (Circuit n)›), c.depth ≤ 0 := by
                -- Since the foldr result is zero, each element's depth must be zero.
                have h_max_zero : ∀ {l : List (Circuit n)}, List.foldr (fun c acc => max c.depth acc) 0 l = 0 → ∀ c ∈ l, c.depth = 0 := by
                  intros l hl c hc; induction l <;> aesop;
                exact fun c hc => le_of_eq ( h_max_zero hc_depth c hc );
              intro c hc; specialize h_children_literals c hc; rcases c with ( _ | ⟨ l ⟩ | ⟨ isAnd, cs ⟩ ) <;> simp_all +decide [ Circuit.depth ] ;
            obtain ⟨lits, hlits⟩ : ∃ lits : List (Lit n), ‹List (Circuit n)› = lits.map (fun l => .lit l) := by
              have h_children_literals : ∀ {l : List (Circuit n)}, (∀ c ∈ l, ∃ l' : Lit n, c = .lit l') → ∃ lits : List (Lit n), l = lits.map (fun l => .lit l) := by
                intros l hl; induction' l with c l ih <;> simp_all +decide [ List.map ] ;
                rcases hl.1 with ⟨ l', rfl ⟩ ; obtain ⟨ lits, rfl ⟩ := ih; exact ⟨ l' :: lits, by simp +decide ⟩ ;
              exact h_children_literals ‹_›;
            simp_all +decide [ depth2AndToCNF ];
            convert foldr_or_lits_eq_clause_eval lits x using 1;
            · rw [ foldr_or_lits_eq_clause_eval ];
              rw [ List.filterMap_congr ];
              rotate_right;
              use fun l => some l.toLiteral;
              · simp +decide [ CNF.eval, CNF.evalClause ];
              · exact fun x hx => rfl;
            · convert foldr_or_lits_eq_clause_eval lits x using 1;
              induction lits <;> simp +decide [ *, Circuit.eval ];
              induction ‹List (Lit n)› <;> simp +decide [ *, Circuit.eval ];
              congr! 2;
              rename_i k hk₁ hk₂;
              exact List.recOn k rfl fun l k ih => by simp +decide [ *, Circuit.eval ] ;
          · -- Since the depth of each child is ≤ 1, each child is either a literal or an OR node with literals.
            have h_children : ∀ c ∈ ‹List (Circuit n)›, ∃ l : Lit n, c = .lit l := by
              have h_children : ∀ c ∈ ‹List (Circuit n)›, c.depth ≤ 0 := by
                intro c hc; contrapose! hc_depth;
                have h_foldr_pos : ∀ {l : List (Circuit n)}, (∃ c ∈ l, 0 < c.depth) → 0 < List.foldr (fun c acc => max c.depth acc) 0 l := by
                  intros l hl; induction l <;> aesop;
                exact ne_of_gt ( h_foldr_pos ⟨ c, hc, hc_depth ⟩ );
              intro c hc; specialize h_children c hc; rcases c with ( _ | ⟨ l ⟩ | ⟨ isAnd, cs ⟩ ) <;> simp_all +decide [ Circuit.depth ] ;
            unfold depth2AndToCNF; simp +decide [ Circuit.eval ] ;
            rename_i k;
            have h_foldr : ∀ (l : List (Circuit n)), (∀ c ∈ l, ∃ l' : Lit n, c = .lit l') → CNF.eval (List.filterMap (fun c' => match c' with | .lit l => some [l.toLiteral] | _ => none) l) x = List.foldr (fun c acc => c.eval x && acc) true l := by
              intro l hl; induction l <;> simp_all +decide [ CNF.eval ] ;
              rcases hl.1 with ⟨ l, rfl ⟩ ; simp +decide [ Circuit.eval ] ;
              unfold CNF.evalClause; simp +decide [ Lit.toLiteral ] ;
              unfold Literal.eval; simp +decide [ Lit.toLiteral ] ;
              cases l.sign <;> simp +decide [ * ];
            exact h_foldr k h_children;
      -- By definition of `depth2AndToCNF`, we can rewrite the left-hand side as the flatMap of the translaton of each child.
      have h_flatMap : (depth2AndToCNF cs).eval x = List.all cs (fun c => CNF.eval (depth2AndToCNF [c]) x) := by
        unfold depth2AndToCNF; simp +decide [ CNF.eval ] ;
      -- Since each child c in cs has depth ≤ 1, we can apply h_child to each child.
      have h_all_child : List.all cs (fun c => CNF.eval (depth2AndToCNF [c]) x) = List.all cs (fun c => c.eval x) := by
        suffices ∀ (l : List (Circuit n)), (∀ c ∈ l, c ∈ cs) →
            List.all l (fun c => CNF.eval (depth2AndToCNF [c]) x) = List.all l (fun c => c.eval x) from
          this cs (fun c hc => hc)
        intro l hl
        induction l with
        | nil => rfl
        | cons c l ih =>
          simp only [List.all_cons]
          have hc : c ∈ cs := hl c (List.mem_cons.mpr (Or.inl rfl))
          rw [h_child c hc (depth_le_two_children_depth_le_one cs true hd c hc)]
          congr 1
          exact ih (fun c' hc' => hl c' (List.mem_cons.mpr (Or.inr hc')))
      -- By definition of `Circuit.node`, the evaluation of a node with true is the conjunction of the evaluations of its children.
      have h_node_true : ∀ (cs : List (Circuit n)), (Circuit.node true cs).eval x = List.all cs (fun c => c.eval x) := by
        intros cs
        simp [Circuit.eval];
        induction cs <;> simp +decide [ * ];
      rw [h_flatMap, h_all_child, h_node_true]

/-
Width bound for depth2OrToDNF.
-/
lemma depth2OrToDNF_width_le (cs : List (Circuit n))
    (hd : (Circuit.node false cs).depth ≤ 2) :
    (depth2OrToDNF cs).width ≤ (Circuit.node false cs).maxFanin := by
      have h_term_width : ∀ c ∈ cs, (match c with
        | Circuit.lit l => 1
        | Circuit.node true cs' => cs'.length
        | Circuit.node false cs' => 1) ≤ (Circuit.node false cs).maxFanin := by
          intro c hc
          have h_c_maxFanin : c.maxFanin ≤ (Circuit.node false cs).maxFanin := by
            have h_max_fanin : ∀ {l : List (Circuit n)}, c ∈ l → c.maxFanin ≤ List.foldr (fun c acc => max c.maxFanin acc) 0 l := by
              intros l hl; induction l <;> aesop;
            exact le_trans ( h_max_fanin hc ) ( by cases cs <;> simp +decide [ Circuit.maxFanin ] );
          cases c <;> simp_all +decide [ Circuit.maxFanin ];
          · exact Or.inl ( List.length_pos_iff.mpr ( by aesop_cat ) );
          · cases ‹Bool› <;> simp_all +decide [ Circuit.maxFanin ]; all_goals grind;
      have h_term_width : ∀ t ∈ List.flatMap (fun c => match c with
        | Circuit.lit l => [[l.toLiteral]]
        | Circuit.node true cs' => [List.filterMap (fun c' => match c' with | Circuit.lit l => some l.toLiteral | _ => none) cs']
        | Circuit.node false cs' => List.filterMap (fun c' => match c' with | Circuit.lit l => some [l.toLiteral] | _ => none) cs') cs, t.length ≤ (Circuit.node false cs).maxFanin := by
          grind +qlia;
      have h_max_width : ∀ {l : List ℕ}, (∀ x ∈ l, x ≤ (Circuit.node false cs).maxFanin) → List.foldr max 0 l ≤ (Circuit.node false cs).maxFanin := by
        intros l hl; induction l <;> aesop;
      convert h_max_width _;
      exact fun x hx => by obtain ⟨ t, ht, rfl ⟩ := List.mem_map.mp hx; exact h_term_width t ht;

/-
Width bound for depth2AndToCNF.
-/
lemma depth2AndToCNF_width_le (cs : List (Circuit n))
    (hd : (Circuit.node true cs).depth ≤ 2) :
    CNF.width (depth2AndToCNF cs) ≤ (Circuit.node true cs).maxFanin := by
      unfold depth2AndToCNF;
      -- By definition of `Circuit.maxFanin`, we know that `Circuit.maxFanin (Circuit.node true cs) = max cs.length (cs.foldr (fun c acc => max c.maxFanin acc) 0)`. Since the maximum fan-in is at least the length of the list, we have `cs.length ≤ Circuit.maxFanin (Circuit.node true cs)`.
      have h_maxFanin_ge_length : ∀ c ∈ cs, c.maxFanin ≤ (Circuit.node true cs).maxFanin := by
        intro c hc;
        have h_maxFanin_ge_length : ∀ {l : List (Circuit n)}, c ∈ l → c.maxFanin ≤ List.foldr (fun c acc => max c.maxFanin acc) 0 l := by
          intros l hl; induction l <;> aesop;
        simp only [Circuit.maxFanin]
        exact le_trans (h_maxFanin_ge_length hc) (le_max_right _ _)
      have h_maxFanin_ge_length : ∀ c ∈ cs, (match c with
        | .lit l => 1
        | .node false cs' => cs'.length
        | .node true cs' => 1) ≤ (Circuit.node true cs).maxFanin := by
          intro c hc
          specialize h_maxFanin_ge_length c hc;
          rcases c with ( _ | _ | _ ) <;> simp +decide [ Circuit.maxFanin ] at h_maxFanin_ge_length ⊢;
          · exact Or.inl ( List.length_pos_iff.mpr ( by aesop_cat ) );
          · grind;
          · grind;
      have h_maxFanin_ge_length : ∀ t ∈ List.flatMap (fun c =>
        match c with
        | .lit l => [[l.toLiteral]]
        | .node false cs' => [cs'.filterMap (fun c' =>
            match c' with
            | .lit l => some l.toLiteral
            | _ => none)]
        | .node true cs' => cs'.filterMap (fun c' =>
            match c' with
            | .lit l => some [l.toLiteral]
            | _ => none)) cs, t.length ≤ (Circuit.node true cs).maxFanin := by
              grind +splitImp;
      have h_maxFanin_ge_length : ∀ {l : List ℕ}, (∀ x ∈ l, x ≤ (Circuit.node true cs).maxFanin) → List.foldr max 0 l ≤ (Circuit.node true cs).maxFanin := by
        intros l hl; induction l <;> aesop;
      convert h_maxFanin_ge_length _;
      exact fun x hx => by obtain ⟨ t, ht, rfl ⟩ := List.mem_map.mp hx; exact ‹∀ t ∈ _, t.length ≤ _› t ht;

end LMN
end