import TCSlib.BooleanAnalysis.Switching.Defs

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

private lemma numFree_update_lt {n : ℕ} (ρ : Restriction n) (v : Fin n) (b : Bool)
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
private noncomputable def termSubTree {n : ℕ} :
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
