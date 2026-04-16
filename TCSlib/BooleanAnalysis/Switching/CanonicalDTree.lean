import TCSlib.BooleanAnalysis.Switching.Restriction
import Mathlib.Tactic.Cases

/-!
# Canonical Decision Tree Construction

The canonical decision tree for `f|ρ`, following Razborov's construction.
At each stage, we find the first term not killed by the current restriction,
build a complete sub-tree over all of that term's free variables, and continue.
-/

open Classical

namespace SwitchingLemma2

variable {n : ℕ}

/-! ## Canonical decision tree helpers -/

lemma numFree_update_lt {n : ℕ} (ρ : Restriction n) (v : Fin n) (b : Bool)
    (hv : v ∈ ρ.freeVars) :
    Restriction.numFree (Function.update ρ v (some b)) < ρ.numFree := by
  simp only [Restriction.numFree]
  apply Finset.card_lt_card
  rw [ssubset_iff_subset_ne]
  constructor
  · intro i hi
    simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    simp only [Function.update] at hi
    split at hi
    · simp at hi
    · exact hi
  · intro heq
    have hv_not : v ∉ Restriction.freeVars (Function.update ρ v (some b)) := by
      simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ, true_and]
      simp [Function.update]
    rw [← heq] at hv
    exact hv_not hv

private lemma exists_free_of_not_killed_not_fixed {n : ℕ} (f : DNF n) (ρ : Restriction n)
    (h1 : ¬∀ t ∈ f, Term.killedBy t ρ) (h2 : ¬∃ t ∈ f, Term.fixedBy t ρ) :
    ∃ v : Fin n, v ∈ ρ.freeVars := by
  by_contra hall
  push_neg at hall
  apply h1; intro t ht
  by_contra ht_nk
  apply h2; refine ⟨t, ht, fun l hl => ?_⟩
  have hass : l.var ∉ ρ.freeVars := hall l.var
  simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ, true_and] at hass
  simp only [Option.isNone_iff_eq_none] at hass
  cases hv : ρ l.var with
  | none => exact absurd hv hass
  | some b =>
    show ρ l.var = some (!l.neg)
    by_cases hbl : b = l.neg
    · exfalso; exact ht_nk ⟨l, hl, by simp only [Literal.killedBy]; rw [hv, hbl]⟩
    · rw [hv]; congr 1
      cases b <;> cases hln : l.neg
      · exfalso; rw [hln] at hbl; exact hbl rfl
      · rfl
      · rfl
      · exfalso; rw [hln] at hbl; exact hbl rfl

noncomputable def selectBranchVar {n : ℕ} (f : DNF n) (ρ : Restriction n) :
    Option (Fin n) :=
  match f.find? (fun t => decide (¬Term.killedBy t ρ)) with
  | none => none
  | some t =>
    match t.find? (fun l => decide (l.var ∈ ρ.freeVars)) with
    | none => none
    | some l => some l.var

private lemma selectBranchVar_spec {n : ℕ} (f : DNF n) (ρ : Restriction n)
    (h1 : ¬∀ t ∈ f, Term.killedBy t ρ) (h2 : ¬∃ t ∈ f, Term.fixedBy t ρ) :
    ∃ v, selectBranchVar f ρ = some v ∧ v ∈ ρ.freeVars := by
  unfold selectBranchVar
  have h1' : f.find? (fun t => decide (¬Term.killedBy t ρ)) ≠ none := by
    intro habs; rw [List.find?_eq_none] at habs
    push_neg at h1; obtain ⟨t, htm, htnk⟩ := h1
    exact (habs t htm) (by simp [htnk])
  obtain ⟨t, ht_eq⟩ : ∃ t, f.find? (fun t => decide (¬Term.killedBy t ρ)) = some t := by
    cases hf : f.find? (fun t => decide (¬Term.killedBy t ρ)) with
    | none => exact absurd hf h1'
    | some t => exact ⟨t, rfl⟩
  simp only [ht_eq]
  have ht_nk : ¬Term.killedBy t ρ := by
    have := List.find?_some ht_eq; simp at this; exact this
  have ht_mem : t ∈ f := List.mem_of_find?_eq_some ht_eq
  have ht_nf : ¬Term.fixedBy t ρ := fun hf => h2 ⟨t, ht_mem, hf⟩
  have h3 : t.find? (fun l => decide (l.var ∈ ρ.freeVars)) ≠ none := by
    intro hall
    rw [List.find?_eq_none] at hall
    apply ht_nf; intro l hl
    have : l.var ∉ ρ.freeVars := by have := hall l hl; simp at this; exact this
    simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ, true_and,
               Option.isNone_iff_eq_none] at this
    cases hv : ρ l.var with
    | none => exact absurd hv this
    | some b =>
      by_cases hbl : b = l.neg
      · exfalso; exact ht_nk ⟨l, hl, by simp only [Literal.killedBy]; rw [hv, hbl]⟩
      · show ρ l.var = some (!l.neg); rw [hv]; congr 1
        cases b <;> simp_all
  obtain ⟨l, hl_eq⟩ : ∃ l, t.find? (fun l => decide (l.var ∈ ρ.freeVars)) = some l := by
    cases hf : t.find? (fun l => decide (l.var ∈ ρ.freeVars)) with
    | none => exact absurd hf h3
    | some l => exact ⟨l, rfl⟩
  simp only [hl_eq]
  exact ⟨l.var, rfl, by have := List.find?_some hl_eq; simp at this; exact this⟩

/-! ## termSubTree -/

/-- Build a complete sub-tree for a term, querying all its free variables
    in order. At each leaf, call the continuation with the updated restriction. -/
noncomputable def termSubTree {n : ℕ} :
    List (Literal n) → Restriction n →
    (Restriction n → DecisionTree n) → DecisionTree n
  | [], ρ, cont => cont ρ
  | l :: rest, ρ, cont =>
    if l.var ∈ ρ.freeVars then
      .branch l.var
        (termSubTree rest (Function.update ρ l.var (some false)) cont)
        (termSubTree rest (Function.update ρ l.var (some true)) cont)
    else
      termSubTree rest ρ cont

/-! ## Canonical decision tree -/

/-- The canonical decision tree for f|ρ, following Razborov's construction. -/
noncomputable def canonicalDTree {n : ℕ} (f : DNF n) (ρ : Restriction n) :
    DecisionTree n :=
  canonicalDTree.go f (ρ.numFree + 1) ρ
where
  go (f : DNF n) : ℕ → Restriction n → DecisionTree n
    | 0, _ => .leaf false
    | fuel + 1, ρ =>
      if _h1 : ∀ t ∈ f, Term.killedBy t ρ then .leaf false
      else if _h2 : ∃ t ∈ f, Term.fixedBy t ρ then .leaf true
      else
        match f.find? (fun t => decide (¬Term.killedBy t ρ)) with
        | none => .leaf false
        | some t =>
          termSubTree t ρ (fun ρ' =>
            if decide (Term.fixedBy t ρ') then .leaf true
            else go f fuel ρ')

/-! ## termSubTree semantics -/

private lemma extend_update_self {n : ℕ} (ρ : Restriction n) (v : Fin n)
    (x : Fin n → Bool) (b : Bool) (hv : v ∈ ρ.freeVars) (hxv : x v = b) :
    Restriction.extend (Function.update ρ v (some b)) x = ρ.extend x := by
  funext i
  simp only [Restriction.extend]
  by_cases h : i = v
  · subst h
    have hfree : ρ i = none := by
      simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ, true_and,
                  Option.isNone_iff_eq_none] at hv
      exact hv
    simp [Function.update, hfree, hxv]
  · simp [Function.update, h]

/-- `termSubTree` preserves the semantics. -/
private lemma termSubTree_eval {n : ℕ} (lits : List (Literal n))
    (ρ : Restriction n) (cont : Restriction n → DecisionTree n) (x : Fin n → Bool) :
    (termSubTree lits ρ cont).eval x =
    (cont (lits.foldl (fun ρ' l =>
      if l.var ∈ ρ'.freeVars then Function.update ρ' l.var (some (x l.var)) else ρ') ρ)).eval x := by
  induction lits generalizing ρ with
  | nil => simp [termSubTree]
  | cons l rest ih =>
    simp only [termSubTree]
    split
    · rename_i hfree
      simp only [DecisionTree.eval]
      cases hxv : x l.var <;> simp [hxv, ih] <;>
        congr 1 <;> simp [List.foldl, hfree, hxv]
    · rename_i hnfree
      rw [ih]; congr 1; simp [List.foldl, hnfree]

/-- After `termSubTree` assigns all free variables from `x`, the resulting
    restriction extends the same as the original. -/
private lemma termSubTree_extend_eq {n : ℕ} (lits : List (Literal n))
    (ρ : Restriction n) (x : Fin n → Bool) :
    (lits.foldl (fun (ρ' : Restriction n) l =>
      if l.var ∈ ρ'.freeVars then Function.update ρ' l.var (some (x l.var))
      else ρ') ρ).extend x = ρ.extend x := by
  induction lits generalizing ρ with
  | nil => rfl
  | cons l rest ih =>
    simp only [List.foldl]
    split
    · rename_i hfree
      rw [ih]; exact extend_update_self ρ l.var x (x l.var) hfree rfl
    · exact ih ρ

/-- The foldl preserves non-none. -/
private lemma termSubTree_foldl_preserves_nonnone {n : ℕ}
    (lits : List (Literal n)) (ρ : Restriction n) (x : Fin n → Bool)
    (v : Fin n) (hv : ρ v ≠ none) :
    (lits.foldl (fun (ρ' : Restriction n) (lit : Literal n) =>
      if lit.var ∈ Restriction.freeVars ρ' then Function.update ρ' lit.var (some (x lit.var))
      else ρ') ρ) v ≠ none := by
  induction lits generalizing ρ with
  | nil => exact hv
  | cons hd tl ih =>
    simp only [List.foldl_cons]; apply ih
    split
    · simp only [Function.update_apply]; split <;> simp_all
    · exact hv

/-- After applying the foldl, a variable that was free and appears in the literal
    list is no longer `none` (it was set to `some`). -/
private lemma termSubTree_foldl_sets_member {n : ℕ}
    (lits : List (Literal n)) (ρ : Restriction n) (x : Fin n → Bool)
    (l : Literal n) (hl : l ∈ lits) (hfree : l.var ∈ ρ.freeVars) :
    (lits.foldl (fun (ρ' : Restriction n) (lit : Literal n) =>
      if lit.var ∈ Restriction.freeVars ρ' then Function.update ρ' lit.var (some (x lit.var))
      else ρ') ρ) l.var ≠ none := by
  induction lits generalizing ρ with
  | nil => simp at hl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hl with rfl | hl_tl
    · apply termSubTree_foldl_preserves_nonnone
      simp only [hfree, ↓reduceIte]
      simp [Function.update]
    · -- l ∈ tl, need to show foldl over (hd :: tl) doesn't set l.var to none
      split
      · -- hd.var ∈ ρ.freeVars
        by_cases heq : l.var = hd.var
        · -- l.var = hd.var: update sets it to some, preserved by foldl
          apply termSubTree_foldl_preserves_nonnone
          rw [Function.update_apply, if_pos heq]
          exact Option.some_ne_none _
        · -- l.var ≠ hd.var: l.var still free after update
          apply ih _ hl_tl
          rw [Restriction.freeVars, Finset.mem_filter] at hfree ⊢
          simp only [Finset.mem_univ, true_and,
            Option.isNone_iff_eq_none] at hfree ⊢
          rw [Function.update_apply, if_neg heq]
          exact hfree
      · -- hd.var ∉ ρ.freeVars: ρ unchanged, use ih directly
        exact ih _ hl_tl hfree

/-- The foldl strictly decreases `numFree` when at least one literal has a free variable. -/
private lemma termSubTree_foldl_numFree_lt {n : ℕ}
    (lits : List (Literal n)) (ρ : Restriction n) (x : Fin n → Bool)
    (l : Literal n) (hl : l ∈ lits) (hfree : l.var ∈ ρ.freeVars) :
    (lits.foldl (fun (ρ' : Restriction n) (lit : Literal n) =>
      if lit.var ∈ Restriction.freeVars ρ' then Function.update ρ' lit.var (some (x lit.var))
      else ρ') ρ).numFree < ρ.numFree := by
  set ρ' := lits.foldl _ ρ
  have hsub : ρ'.freeVars ⊆ ρ.freeVars := by
    intro v hv
    simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ, true_and,
      Option.isNone_iff_eq_none] at hv ⊢
    by_contra h; push_neg at h
    exact absurd hv (termSubTree_foldl_preserves_nonnone lits ρ x v h)
  have hne : l.var ∉ ρ'.freeVars := by
    simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ, true_and,
      Option.isNone_iff_eq_none]
    exact termSubTree_foldl_sets_member lits ρ x l hl hfree
  exact Finset.card_lt_card (hsub.ssubset_of_ne (fun heq => hne (heq ▸ hfree)))

/-! ## Canonical decision tree correctness -/

private lemma canonicalDTree_go_correct {n : ℕ} (f : DNF n) (fuel : ℕ) (ρ : Restriction n)
    (hfuel : ρ.numFree < fuel) :
    ∀ x, (canonicalDTree.go f fuel ρ).eval x = restrictFn f.eval ρ x := by
  intro x
  induction fuel generalizing ρ with
  | zero => omega
  | succ k ih =>
    simp only [canonicalDTree.go]
    split
    · rename_i h1
      simp only [DecisionTree.eval, restrictFn, DNF.eval]; symm
      apply list_any_eq_false; intro t ht
      show t.eval (ρ.extend x) = false
      obtain ⟨l, hl_mem, hl_killed⟩ := h1 t ht
      simp only [Term.eval]
      exact list_all_eq_false_of_mem hl_mem (Literal.killedBy_eval_false l ρ hl_killed x)
    · split
      · rename_i _ h2
        simp only [DecisionTree.eval, restrictFn, DNF.eval]
        obtain ⟨t, ht_mem, ht_fixed⟩ := h2; symm; rw [List.any_eq_true]
        refine ⟨t, ht_mem, ?_⟩; show t.eval (ρ.extend x) = true
        rw [Term.eval, List.all_eq_true]
        exact fun l hl => Literal.fixedBy_eval_true l ρ (ht_fixed l hl) x
      · rename_i h1 h2; split
        · rename_i hfind; exfalso; apply h1; intro t ht
          by_contra htk; rw [List.find?_eq_none] at hfind
          exact (hfind t ht) (by simp [htk])
        · rename_i t hfind
          set ρ' := t.foldl (fun (ρ' : Restriction n) l =>
            if l.var ∈ ρ'.freeVars then Function.update ρ' l.var (some (x l.var))
            else ρ') ρ
          rw [termSubTree_eval]
          have hext : ρ'.extend x = ρ.extend x := termSubTree_extend_eq t ρ x
          split
          · rename_i ht_fixed
            simp only [DecisionTree.eval, restrictFn, DNF.eval]
            have ht_fixed' : Term.fixedBy t ρ' := of_decide_eq_true ht_fixed
            symm; rw [List.any_eq_true]
            refine ⟨t, List.mem_of_find?_eq_some hfind, ?_⟩
            show t.eval (ρ.extend x) = true
            rw [← hext, Term.eval, List.all_eq_true]
            exact fun l hl => Literal.fixedBy_eval_true l ρ' (ht_fixed' l hl) x
          · rename_i ht_not_fixed
            have hres : restrictFn f.eval ρ' x = restrictFn f.eval ρ x := by
              simp only [restrictFn]; rw [hext]
            have hρ'_lt : ρ'.numFree < k := by
              have hle : ρ.numFree ≤ k := Nat.lt_succ_iff.mp hfuel
              have ht_nk : ¬Term.killedBy t ρ := by
                have := List.find?_some hfind; simp at this; exact this
              have ht_nf : ¬Term.fixedBy t ρ :=
                fun hf => h2 ⟨t, List.mem_of_find?_eq_some hfind, hf⟩
              have ⟨l, hl_mem, hl_free⟩ : ∃ l ∈ t, l.var ∈ ρ.freeVars := by
                by_contra hall; push_neg at hall; apply ht_nf; intro l hl
                have : l.var ∉ ρ.freeVars := hall l hl
                simp [Restriction.freeVars, Finset.mem_filter, Option.isNone_iff_eq_none] at this
                cases hv : ρ l.var with
                | none => exact absurd hv this
                | some b =>
                  by_cases hbl : b = l.neg
                  · exact absurd ⟨l, hl, by rw [Literal.killedBy, hv, hbl]⟩ ht_nk
                  · show ρ l.var = some (!l.neg); rw [hv]; congr 1
                    cases b <;> cases hn : l.neg <;> simp_all [hn]
              exact lt_of_lt_of_le
                (termSubTree_foldl_numFree_lt t ρ x l hl_mem hl_free) hle
            change (canonicalDTree.go f k ρ').eval x = _
            rw [ih ρ' hρ'_lt, hres]

lemma canonicalDTree_correct {n : ℕ} (f : DNF n) (ρ : Restriction n) :
    ∀ x, (canonicalDTree f ρ).eval x = restrictFn f.eval ρ x :=
  canonicalDTree_go_correct f _ ρ (Nat.lt_succ_of_le (le_refl _))

/-! ## Fuel invariance -/

/-- Updating at a variable cannot increase `numFree`. -/
private lemma numFree_update_le {n : ℕ} (ρ : Restriction n) (v : Fin n) (b : Bool) :
    Restriction.numFree (Function.update ρ v (some b)) ≤ ρ.numFree := by
  simp only [Restriction.numFree]
  apply Finset.card_le_card
  intro i hi
  simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ, true_and,
             Option.isNone_iff_eq_none] at hi ⊢
  rw [Function.update_apply] at hi
  split at hi
  · simp at hi
  · exact hi

/-- `termSubTree` is extensional in its continuation: if two continuations
    agree on all restrictions `ρ'` with `ρ'.numFree ≤ ρ.numFree`, the
    resulting trees are equal. -/
private lemma termSubTree_cont_congr {n : ℕ} :
    ∀ (lits : List (Literal n)) (ρ : Restriction n)
      (cont₁ cont₂ : Restriction n → DecisionTree n)
      (_ : ∀ ρ', ρ'.numFree ≤ ρ.numFree → cont₁ ρ' = cont₂ ρ'),
      termSubTree lits ρ cont₁ = termSubTree lits ρ cont₂
  | [], ρ, cont₁, cont₂, hcont => by
      show cont₁ ρ = cont₂ ρ
      exact hcont ρ (le_refl _)
  | l :: rest, ρ, cont₁, cont₂, hcont => by
      by_cases hfree : l.var ∈ ρ.freeVars
      · simp only [termSubTree, hfree, ↓reduceIte]
        congr 1
        · apply termSubTree_cont_congr rest _ cont₁ cont₂
          intro ρ' hρ'
          exact hcont ρ' (le_trans hρ'
            (numFree_update_le ρ l.var false))
        · apply termSubTree_cont_congr rest _ cont₁ cont₂
          intro ρ' hρ'
          exact hcont ρ' (le_trans hρ'
            (numFree_update_le ρ l.var true))
      · simp only [termSubTree, hfree, ↓reduceIte]
        exact termSubTree_cont_congr rest ρ cont₁ cont₂ hcont

/-- Strict version: if `lits` contains at least one literal free in ρ,
    then the required agreement on continuations is strict — we only
    need cont₁ and cont₂ to agree on ρ' with `ρ'.numFree < ρ.numFree`. -/
private lemma termSubTree_cont_congr_strict {n : ℕ} :
    ∀ (lits : List (Literal n)) (ρ : Restriction n)
      (_ : ∃ l ∈ lits, l.var ∈ ρ.freeVars)
      (cont₁ cont₂ : Restriction n → DecisionTree n)
      (_ : ∀ ρ', ρ'.numFree < ρ.numFree → cont₁ ρ' = cont₂ ρ'),
      termSubTree lits ρ cont₁ = termSubTree lits ρ cont₂
  | [], _, hex, _, _, _ => by
      obtain ⟨_, hl, _⟩ := hex
      exact absurd hl (List.not_mem_nil)
  | l :: rest, ρ, hex, cont₁, cont₂, hcont => by
      by_cases hfree : l.var ∈ ρ.freeVars
      · -- Free case: descend into both branches via non-strict congr.
        -- Updating at l.var strictly decreases numFree.
        simp only [termSubTree, hfree, ↓reduceIte]
        have hupd_lt_false : Restriction.numFree (Function.update ρ l.var (some false)) <
            ρ.numFree := numFree_update_lt ρ l.var false hfree
        have hupd_lt_true : Restriction.numFree (Function.update ρ l.var (some true)) <
            ρ.numFree := numFree_update_lt ρ l.var true hfree
        congr 1
        · apply termSubTree_cont_congr rest _ cont₁ cont₂
          intro ρ' hρ'
          exact hcont ρ' (Nat.lt_of_le_of_lt hρ' hupd_lt_false)
        · apply termSubTree_cont_congr rest _ cont₁ cont₂
          intro ρ' hρ'
          exact hcont ρ' (Nat.lt_of_le_of_lt hρ' hupd_lt_true)
      · -- Non-free case: skip; apply IH on rest with smaller hex.
        simp only [termSubTree, hfree, ↓reduceIte]
        have hex' : ∃ l' ∈ rest, l'.var ∈ ρ.freeVars := by
          obtain ⟨l', hl'_mem, hl'_free⟩ := hex
          rcases List.mem_cons.mp hl'_mem with rfl | hl'_tl
          · exact absurd hl'_free hfree
          · exact ⟨l', hl'_tl, hl'_free⟩
        exact termSubTree_cont_congr_strict rest ρ hex' cont₁ cont₂ hcont

/-- **Fuel invariance of `canonicalDTree.go`**: once `fuel > ρ.numFree`, the
    resulting tree does not depend on the exact fuel. -/
lemma canonicalDTree_go_fuel_invariant {n : ℕ} (f : DNF n) :
    ∀ (k : ℕ) (ρ : Restriction n) (fuel₁ fuel₂ : ℕ)
      (_ : ρ.numFree = k) (_ : ρ.numFree < fuel₁) (_ : ρ.numFree < fuel₂),
      canonicalDTree.go f fuel₁ ρ = canonicalDTree.go f fuel₂ ρ := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro ρ fuel₁ fuel₂ hk h₁ h₂
    -- Both fuels are positive.
    obtain ⟨f₁, rfl⟩ : ∃ f₁, fuel₁ = f₁ + 1 := ⟨fuel₁ - 1, by omega⟩
    obtain ⟨f₂, rfl⟩ : ∃ f₂, fuel₂ = f₂ + 1 := ⟨fuel₂ - 1, by omega⟩
    -- Unfold both `go`s.
    simp only [canonicalDTree.go]
    split_ifs with hkilled hfixed
    · rfl
    · rfl
    · -- Alive branch.
      split
      · rfl
      · rename_i t hfind
        -- t has a free literal in ρ (since it's not killed and not fixed).
        have ht_nk : ¬ Term.killedBy t ρ := by
          have := List.find?_some hfind; simp at this; exact this
        have ht_mem : t ∈ f := List.mem_of_find?_eq_some hfind
        have ht_nf : ¬ Term.fixedBy t ρ := fun hf => hfixed ⟨t, ht_mem, hf⟩
        have hex : ∃ l ∈ t, l.var ∈ ρ.freeVars := by
          by_contra hall
          push_neg at hall
          apply ht_nf
          intro l hl
          have hlnf : l.var ∉ ρ.freeVars := hall l hl
          simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ,
                     true_and, Option.isNone_iff_eq_none] at hlnf
          cases hv : ρ l.var with
          | none => exact absurd hv hlnf
          | some b =>
            show ρ l.var = some (!l.neg)
            by_cases hbl : b = l.neg
            · exact absurd ⟨l, hl, by rw [Literal.killedBy, hv, hbl]⟩ ht_nk
            · rw [hv]; congr 1
              cases b <;> cases hn : l.neg <;> simp_all
        -- Apply `termSubTree_cont_congr_strict` directly, avoiding `congr`.
        exact termSubTree_cont_congr_strict t ρ hex _ _ (by
          intro ρ' hρ'
          by_cases hfix : decide (Term.fixedBy t ρ')
          · simp only [hfix, ↓reduceIte]
          · simp only [hfix, ↓reduceIte]
            have hρ'_lt_k : ρ'.numFree < k := hk ▸ hρ'
            exact ih ρ'.numFree hρ'_lt_k ρ' f₁ f₂ rfl
              (by omega) (by omega))

/-! ### Self-similarity of canonicalDTree -/

/-
The continuation of termSubTree at the restriction reached after traversing
    all free literals yields a tree whose deepPath matches `canonicalDTree f ρ'`.

    Specifically, if `cont = fun ρ' => if fixedBy t ρ' then leaf true else go f fuel ρ'`
    with `fuel ≥ ρ'.numFree + 1`, then `cont ρ'` and `canonicalDTree f ρ'` are
    identical, because:
    - If `fixedBy t ρ'`: `cont ρ'` is `leaf true`, and `canonicalDTree f ρ'` is
      `leaf true` (since `t ∈ f` and `fixedBy t ρ'` means the fixed-clause
      check fires).
    - If `¬fixedBy t ρ'`: `cont ρ'` is `go f fuel ρ'`, and `canonicalDTree f ρ'`
      is `go f (ρ'.numFree + 1) ρ'`. By `canonicalDTree_go_fuel_invariant`,
      these are equal.
-/
lemma cont_eq_canonicalDTree {n : ℕ} (f : DNF n) (ρ_orig : Restriction n)
    (t : Term n) (ht_mem : t ∈ f) (ρ' : Restriction n)
    (hfuel : ρ_orig.numFree ≥ ρ'.numFree + 1) :
    (if decide (Term.fixedBy t ρ') then DecisionTree.leaf true
     else canonicalDTree.go f ρ_orig.numFree ρ') =
    canonicalDTree f ρ' := by
  split_ifs <;> simp_all +decide [ SwitchingLemma2.canonicalDTree ];
  · rw [ SwitchingLemma2.canonicalDTree.go ];
    split_ifs;
    · have := ‹∀ t ∈ f, Term.killedBy t ρ'› t ht_mem;
      obtain ⟨ l, hl₁, hl₂ ⟩ := this;
      exact absurd ( ‹Term.fixedBy t ρ'› l hl₁ ) ( by unfold Literal.fixedBy; unfold Literal.killedBy at hl₂; aesop );
    · rfl;
    · exact False.elim <| ‹¬∃ t ∈ f, Term.fixedBy t ρ'› ⟨ t, ht_mem, by assumption ⟩;
  · apply SwitchingLemma2.canonicalDTree_go_fuel_invariant;
    exacts [ rfl, hfuel, Nat.lt_succ_self _ ]

/-! ## Depth bounds -/

/-! ## termSubTree deepPath structural lemmas -/

/-- Unfolding `termSubTree` at a free-variable head literal: it produces a
    `.branch` splitting on `l.var`, with both children being recursive
    `termSubTree` calls on the updated restrictions. -/
lemma termSubTree_cons_free {n : ℕ}
    (l : Literal n) (rest : List (Literal n)) (ρ : Restriction n)
    (cont : Restriction n → DecisionTree n)
    (hfree : l.var ∈ ρ.freeVars) :
    termSubTree (l :: rest) ρ cont = .branch l.var
      (termSubTree rest (Function.update ρ l.var (some false)) cont)
      (termSubTree rest (Function.update ρ l.var (some true)) cont) := by
  simp [termSubTree, hfree]

/-- Unfolding `termSubTree` at a non-free head literal: the literal is
    skipped and recursion continues on the tail. -/
lemma termSubTree_cons_nonfree {n : ℕ}
    (l : Literal n) (rest : List (Literal n)) (ρ : Restriction n)
    (cont : Restriction n → DecisionTree n)
    (hnfree : l.var ∉ ρ.freeVars) :
    termSubTree (l :: rest) ρ cont = termSubTree rest ρ cont := by
  simp [termSubTree, hnfree]

/-- **deepPath head extraction for `termSubTree`**: when the head literal
    is free in ρ, the deepest root-to-leaf path begins with `(l.var, b)`
    where `b` is the direction of the deeper child (with ties broken
    toward `true` by `deepPath`'s definition). -/
lemma termSubTree_deepPath_head_free {n : ℕ}
    (l : Literal n) (rest : List (Literal n)) (ρ : Restriction n)
    (cont : Restriction n → DecisionTree n)
    (hfree : l.var ∈ ρ.freeVars) :
    ∃ b, (termSubTree (l :: rest) ρ cont).deepPath =
      (l.var, b) :: (termSubTree rest (Function.update ρ l.var (some b)) cont).deepPath := by
  rw [termSubTree_cons_free l rest ρ cont hfree]
  -- .branch l.var lo hi where:
  --   lo = termSubTree rest (update false) cont
  --   hi = termSubTree rest (update true) cont
  -- deepPath picks the deeper side (ties → true).
  simp only [DecisionTree.deepPath]
  split
  · -- hi.depth ≥ lo.depth: take true branch
    exact ⟨true, rfl⟩
  · -- hi.depth < lo.depth: take false branch
    exact ⟨false, rfl⟩

/-
When variables in `lits` are pairwise distinct, updating ρ at one variable
    does not change the freeness of the others.
-/
lemma filter_free_update_eq {n : ℕ}
    (rest : List (Literal n)) (ρ : Restriction n) (v : Fin n) (b : Bool)
    (hdist : ∀ l ∈ rest, l.var ≠ v) :
    rest.filter (fun l => decide (l.var ∈ Restriction.freeVars (Function.update ρ v (some b)))) =
    rest.filter (fun l => decide (l.var ∈ ρ.freeVars)) := by
  -- Since the variables in `rest` are pairwise distinct and `v` is not in `rest`, the freeness of `l.var` under `Function.update ρ v (some b)` is the same as under `ρ`.
  have h_free_eq : ∀ l ∈ rest, (l.var ∈ Restriction.freeVars (Function.update ρ v (some b))) = (l.var ∈ ρ.freeVars) := by
    unfold Restriction.freeVars; aesop;
  exact List.filter_congr fun x hx => by specialize h_free_eq x hx; aesop;

/-
For termSubTree with distinct-variable literals, the k-th deepPath variable
    matches the k-th free literal's variable.
-/
lemma termSubTree_deepPath_var_match {n : ℕ} :
    ∀ (lits : List (Literal n)) (ρ : Restriction n)
      (cont : Restriction n → DecisionTree n)
      (hdistinct : lits.Pairwise (fun l₁ l₂ => l₁.var ≠ l₂.var))
      (k : ℕ)
      (hk : k < (lits.filter (fun l => decide (l.var ∈ ρ.freeVars))).length)
      (hk_path : k < (termSubTree lits ρ cont).deepPath.length),
      ((termSubTree lits ρ cont).deepPath[k]'hk_path).1 =
        ((lits.filter (fun l => decide (l.var ∈ ρ.freeVars)))[k]'hk).var := by
  intro lits ρ cont hdistinct k hk hk_path; induction' lits with l rest ih generalizing ρ cont k <;> simp +decide [ List.filter_cons ] ;
  · contradiction;
  · by_cases hfree : l.var ∈ ρ.freeVars <;> simp +decide [ hfree ] at hk hk_path ⊢;
    · obtain ⟨b, hb⟩ : ∃ b, (termSubTree (l :: rest) ρ cont).deepPath = (l.var, b) :: (termSubTree rest (Function.update ρ l.var (some b)) cont).deepPath :=
        termSubTree_deepPath_head_free l rest ρ cont hfree
      rcases k with ( _ | k ) <;> simp +decide [ hb ] at hk_path ⊢;
      convert ih ( Function.update ρ l.var ( some b ) ) cont _ k _ hk_path using 1;
      any_goals rw [ filter_free_update_eq ];
      any_goals linarith;
      any_goals rw [ List.pairwise_cons ] at hdistinct; tauto;
      congr! 2;
      refine' List.filter_congr fun x hx => _;
      by_cases h : x.var = l.var <;> simp_all +decide [ Restriction.freeVars ];
      exact hdistinct.1 x hx h.symm;
    · have heq := termSubTree_cons_nonfree l rest ρ cont hfree
      simp only [heq] at hk_path ⊢
      exact ih ρ cont (List.pairwise_cons.mp hdistinct).2 k hk hk_path

/-
The deepPath of `termSubTree` decomposes into entries for the free literals
    followed by the continuation's deepPath at the resulting restriction.
-/
lemma termSubTree_deepPath_append {n : ℕ} :
    ∀ (lits : List (Literal n)) (ρ : Restriction n)
      (cont : Restriction n → DecisionTree n)
      (hdistinct : lits.Pairwise (fun l₁ l₂ => l₁.var ≠ l₂.var)),
      ∃ (ρ' : Restriction n),
        (∀ v, v ∉ (lits.map Literal.var).toFinset → (ρ' v = ρ v)) ∧
        (termSubTree lits ρ cont).deepPath.length =
          (lits.filter (fun l => decide (l.var ∈ ρ.freeVars))).length +
          (cont ρ').deepPath.length := by
  intro lits ρ cont hdistinct; induction' lits with l lits ih generalizing ρ cont; simp_all +decide ;
  · exact ⟨ ρ, fun _ => rfl, rfl ⟩;
  · by_cases hfree : l.var ∈ ρ.freeVars;
    · -- The deepPath of the branch is the deepPath of the chosen branch plus one.
      have h_branch : ∃ b : Bool, (termSubTree (l :: lits) ρ cont).deepPath = (l.var, b) :: (termSubTree lits (Function.update ρ l.var (some b)) cont).deepPath := by
        convert termSubTree_deepPath_head_free l lits ρ cont hfree using 1;
      obtain ⟨ b, hb ⟩ := h_branch;
      obtain ⟨ ρ', hρ', hρ'' ⟩ := ih ( Function.update ρ l.var ( some b ) ) cont ( List.Pairwise.tail hdistinct ) ; use ρ'; simp_all +decide [ List.filter_cons ] ;
      rw [ add_right_comm, filter_free_update_eq ];
      exact fun x hx => Ne.symm ( hdistinct.1 x hx );
    · rw [ termSubTree_cons_nonfree ];
      · obtain ⟨ ρ', hρ₁, hρ₂ ⟩ := ih ρ cont ( List.pairwise_cons.mp hdistinct |>.2 ) ; use ρ'; simp_all +decide [ List.filter_cons ] ;
      · assumption

/-
The deepPath of `termSubTree` splits into a prefix (for the free literals)
    appended with the continuation's deepPath.
-/
lemma termSubTree_deepPath_split {n : ℕ} :
    ∀ (lits : List (Literal n)) (ρ : Restriction n)
      (cont : Restriction n → DecisionTree n)
      (hdistinct : lits.Pairwise (fun l₁ l₂ => l₁.var ≠ l₂.var)),
      ∃ (prefix_dp : List (Fin n × Bool)) (ρ' : Restriction n),
        (termSubTree lits ρ cont).deepPath = prefix_dp ++ (cont ρ').deepPath ∧
        prefix_dp.length = (lits.filter (fun l => decide (l.var ∈ ρ.freeVars))).length ∧
        (∀ v, v ∉ (lits.map Literal.var).toFinset → ρ' v = ρ v) := by
  intro lits ρ cont hdistinct
  induction' lits with l lits ih generalizing ρ cont;
  · exact ⟨ [ ], ρ, rfl, rfl, fun _ _ => rfl ⟩;
  · by_cases hfree : l.var ∈ ρ.freeVars;
    · obtain ⟨ b, hb ⟩ := termSubTree_deepPath_head_free l lits ρ cont hfree;
      obtain ⟨ prefix_dp, ρ', h₁, h₂, h₃ ⟩ := ih ( Function.update ρ l.var ( some b ) ) cont ( List.pairwise_cons.mp hdistinct |>.2 ) ; use ( l.var, b ) :: prefix_dp, ρ'; simp_all +decide [ List.filter_cons ] ;
      rw [ filter_free_update_eq ];
      exact fun x hx => Ne.symm ( hdistinct.1 x hx );
    · rw [ termSubTree_cons_nonfree ];
      · obtain ⟨ prefix_dp, ρ', h₁, h₂, h₃ ⟩ := ih ρ cont ( List.pairwise_cons.mp hdistinct |>.2 ) ; use prefix_dp, ρ'; simp_all +decide [ List.filter_cons ] ;
      · assumption

/-- **`canonicalDTree.go` in the alive branch delegates to `termSubTree`**.
    When the three guards (killed/fixed/find?) take us to the alive branch
    and the first non-killed clause is `t`, `canonicalDTree.go f (fuel+1) ρ`
    unfolds to `termSubTree t ρ cont` where `cont` is the standard
    "fixed? → leaf true; else recurse" continuation. -/
lemma canonicalDTree_alive_eq_termSubTree {n : ℕ} (f : DNF n) (ρ : Restriction n)
    (fuel : ℕ)
    (h1 : ¬ ∀ t ∈ f, Term.killedBy t ρ)
    (h2 : ¬ ∃ t ∈ f, Term.fixedBy t ρ)
    (t : Term n)
    (hfind : f.find? (fun t => decide (¬Term.killedBy t ρ)) = some t) :
    canonicalDTree.go f (fuel + 1) ρ =
      termSubTree t ρ (fun ρ' =>
        if decide (Term.fixedBy t ρ') then .leaf true
        else canonicalDTree.go f fuel ρ') := by
  simp only [canonicalDTree.go]
  rw [dif_neg h1, dif_neg h2]
  rw [hfind]

/-- **`canonicalDTree f ρ` in the alive branch unfolds to `termSubTree`**.
    Top-level wrapper around `canonicalDTree_alive_eq_termSubTree` for
    `canonicalDTree` itself (not `canonicalDTree.go`). -/
lemma canonicalDTree_alive_eq_termSubTree' {n : ℕ} (f : DNF n) (ρ : Restriction n)
    (h1 : ¬ ∀ t ∈ f, Term.killedBy t ρ)
    (h2 : ¬ ∃ t ∈ f, Term.fixedBy t ρ)
    (t : Term n)
    (hfind : f.find? (fun t => decide (¬Term.killedBy t ρ)) = some t) :
    canonicalDTree f ρ =
      termSubTree t ρ (fun ρ' =>
        if decide (Term.fixedBy t ρ') then .leaf true
        else canonicalDTree.go f ρ.numFree ρ') := by
  show canonicalDTree.go f (ρ.numFree + 1) ρ = _
  exact canonicalDTree_alive_eq_termSubTree f ρ ρ.numFree h1 h2 t hfind

/-- Skipping a non-free prefix in `termSubTree`. -/
private lemma termSubTree_skip_nonfree_prefix' {n : ℕ}
    (prefix_lits : List (Literal n)) (rest : List (Literal n))
    (ρ : Restriction n) (cont : Restriction n → DecisionTree n)
    (hnonfree : ∀ l ∈ prefix_lits, l.var ∉ Restriction.freeVars ρ) :
    termSubTree (prefix_lits ++ rest) ρ cont = termSubTree rest ρ cont := by
  induction prefix_lits with
  | nil => simp
  | cons l rest' ih =>
    rw [List.cons_append]
    rw [termSubTree_cons_nonfree l _ ρ cont (hnonfree l List.mem_cons_self)]
    exact ih (fun l' hl' => hnonfree l' (List.mem_cons_of_mem _ hl'))

/-- **Auxiliary (ii)**: `termSubTree t (update ρ l.var (some b))` skips the
    now-fixed `l.var` and proceeds through the remaining literals. Specifically,
    `termSubTree (l :: rest_lits) (update ρ l.var (some b)) cont` equals
    `termSubTree rest_lits (update ρ l.var (some b)) cont` because after the
    update, `l.var ∉ (update ρ l.var (some b)).freeVars`, so `termSubTree`
    takes the non-free branch at `l`. -/
private lemma termSubTree_skip_updated_head {n : ℕ}
    (l : Literal n) (rest_lits : List (Literal n))
    (ρ : Restriction n) (cont : Restriction n → DecisionTree n)
    (v : Fin n) (b : Bool) (hv_eq : l.var = v) :
    termSubTree (l :: rest_lits) (Function.update ρ v (some b)) cont =
    termSubTree rest_lits (Function.update ρ v (some b)) cont := by
  apply termSubTree_cons_nonfree
  rw [← hv_eq]
  simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ, true_and,
             Option.isNone_iff_eq_none, Function.update_apply, ite_eq_left_iff]
  simp

/-! ## Depth bounds -/

lemma depth_ge_dtDepth {n : ℕ} {f : (Fin n → Bool) → Bool}
    (T : DecisionTree n) (heval : ∀ x, T.eval x = f x) :
    T.depth ≥ dtDepth f := by
  unfold dtDepth
  exact Nat.find_min' _ ⟨T, le_refl _, heval⟩

lemma canonicalDTree_depth_ge {n : ℕ} (f : DNF n) (ρ : Restriction n) :
    (canonicalDTree f ρ).depth ≥ dtDepth (restrictFn f.eval ρ) :=
  depth_ge_dtDepth _ (canonicalDTree_correct f ρ)

/-! ## dtDepth upper bound -/

lemma dtDepth_restrictFn_le_numFree {n : ℕ} (f : (Fin n → Bool) → Bool)
    (ρ : Restriction n) :
    dtDepth (restrictFn f ρ) ≤ ρ.numFree := by
  suffices h : ∀ k (ρ : Restriction n), ρ.numFree ≤ k →
      ∃ T : DecisionTree n, T.depth ≤ k ∧ ∀ x, T.eval x = restrictFn f ρ x by
    obtain ⟨T, hT, hev⟩ := h ρ.numFree ρ le_rfl
    exact (depth_ge_dtDepth T hev).trans hT
  intro k
  induction k with
  | zero =>
    intro ρ hρ
    have hempty : ρ.freeVars = ∅ := by
      apply Finset.card_eq_zero.mp
      show ρ.numFree = 0
      omega
    refine ⟨.leaf (f (ρ.extend (fun _ => false))), le_rfl, fun x => ?_⟩
    simp only [DecisionTree.eval, restrictFn]
    congr 1
    funext i
    have hi : ρ i ≠ none := by
      intro hn
      have hmem : i ∈ ρ.freeVars := by
        simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ, true_and,
                   Option.isNone_iff_eq_none]
        exact hn
      rw [hempty] at hmem
      exact Finset.notMem_empty _ hmem
    simp only [Restriction.extend]
    cases hv : ρ i with
    | none => exact absurd hv hi
    | some b => rfl
  | succ k ih =>
    intro ρ hρ
    by_cases hne : ρ.freeVars.Nonempty
    · obtain ⟨v, hv⟩ := hne
      have h0 : Restriction.numFree (Function.update ρ v (some false)) < ρ.numFree :=
        numFree_update_lt ρ v false hv
      have h1 : Restriction.numFree (Function.update ρ v (some true)) < ρ.numFree :=
        numFree_update_lt ρ v true hv
      obtain ⟨T0, hd0, hev0⟩ := ih (Function.update ρ v (some false)) (by omega)
      obtain ⟨T1, hd1, hev1⟩ := ih (Function.update ρ v (some true)) (by omega)
      refine ⟨.branch v T0 T1, ?_, fun x => ?_⟩
      · simp only [DecisionTree.depth]; omega
      · simp only [DecisionTree.eval]
        cases hxv : x v with
        | false =>
          simp only [hxv, Bool.false_eq_true, if_false]
          rw [hev0]
          simp only [restrictFn]
          rw [extend_update_self ρ v x false hv hxv]
        | true =>
          simp only [hxv, if_true]
          rw [hev1]
          simp only [restrictFn]
          rw [extend_update_self ρ v x true hv hxv]
    · have hempty : ρ.freeVars = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hρ0 : ρ.numFree ≤ k := by
        have hz : ρ.numFree = 0 := by
          simp [Restriction.numFree, hempty]
        omega
      obtain ⟨T, hT, hev⟩ := ih ρ hρ0
      exact ⟨T, hT.trans (Nat.le_succ _), hev⟩

end SwitchingLemma2
