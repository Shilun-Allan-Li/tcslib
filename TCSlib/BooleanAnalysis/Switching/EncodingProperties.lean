import TCSlib.BooleanAnalysis.Switching.Encoding

/-!
# Encoding and Decoding Properties

Stability, bounds, and independence lemmas for `processClauseLits`,
`razborovEncode.go`, and `razborovDecode.processEntries`.
-/

open Classical

namespace SwitchingLemma2

variable {n : ℕ}

/-! ## processClauseLits bounds -/

/-- `processClauseLits` produces at most `2 * path.length` combined output. -/
private lemma processClauseLits_bound {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) :
    (processClauseLits lits path ρ₀ σ).2.2.2.length +
    2 * (processClauseLits lits path ρ₀ σ).1.length ≤ 2 * path.length := by
  induction lits generalizing path ρ₀ σ with
  | nil => simp [processClauseLits]
  | cons hd tl ih =>
    cases path with
    | nil => simp [processClauseLits]
    | cons p ps =>
      simp only [processClauseLits, List.length_cons]
      have := ih ps (Function.update ρ₀ hd.1.var (some p.2))
                    (Function.update σ hd.1.var (some (!hd.1.neg)))
      omega

/-- Tight bound for non-empty inputs. -/
private lemma processClauseLits_tight {n : ℕ}
    (fl : Literal n × ℕ) (fls : List (Literal n × ℕ))
    (step : Fin n × Bool) (rest : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) :
    (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ).2.2.2.length + 1 +
    2 * (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ).1.length ≤
    2 * (step :: rest).length := by
  simp only [processClauseLits, List.length_cons]
  have := processClauseLits_bound fls rest
    (Function.update ρ₀ fl.1.var (some step.2))
    (Function.update σ fl.1.var (some (!fl.1.neg)))
  omega

/-! ## Encoding output length bound -/

/-- Bound on `razborovEncode.go` output length. -/
private lemma encode_go_aux_length_bound {n : ℕ} (f : DNF n) (w : ℕ)
    (fuel : ℕ) (path : List (Fin n × Bool)) (ρ₀ σ : Restriction n)
    (acc : List (ℕ × Bool)) :
    (razborovEncode.go f w fuel path ρ₀ σ acc).2.length ≤
    acc.length + 2 * path.length := by
  induction fuel generalizing path ρ₀ σ acc with
  | zero =>
    cases path with
    | nil => simp [razborovEncode.go]
    | cons _ _ => simp [razborovEncode.go]
  | succ fuel ih =>
    cases path with
    | nil => simp [razborovEncode.go]
    | cons step rest =>
      simp only [razborovEncode.go]
      split
      · simp;
      · split
        · simp;
        · next fl fls _ =>
          apply le_trans (ih _ _ _ _)
          simp only [List.length_append, List.length_cons,
                     List.length_nil, Nat.add_zero]
          have := processClauseLits_tight fl fls step rest ρ₀ σ
          have : (step :: rest).length = rest.length + 1 := List.length_cons
          omega

lemma razborovEncode_aux_length_le {n : ℕ} (f : DNF n) (w d : ℕ) (ρ : Restriction n)
    (hbad : IsBadRestriction f.eval d ρ) :
    (razborovEncode f w d ρ).2.length ≤ 2 * d := by
  show (razborovEncode.go f w _ _ ρ ρ []).2.length ≤ 2 * d
  calc (razborovEncode.go f w _ _ ρ ρ []).2.length
      ≤ 0 + 2 * ((canonicalDTree f ρ).deepPath.take d).length :=
        encode_go_aux_length_bound f w _ _ ρ ρ []
    _ ≤ 2 * d := by
        have := List.length_take_le d (canonicalDTree f ρ).deepPath
        omega

/-! ## processClauseLits stability lemmas -/

/-- `processClauseLits` preserves σ at variables not in the literal list. -/
lemma processClauseLits_sigma_stable {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) (v : Fin n) (hv : ∀ p ∈ lits, p.1.var ≠ v) :
    (processClauseLits lits path ρ₀ σ).2.2.1 v = σ v := by
  induction lits generalizing path ρ₀ σ with
  | nil => simp [processClauseLits]
  | cons hd tl ih =>
    cases path with
    | nil => simp [processClauseLits]
    | cons p ps =>
      simp only [processClauseLits]
      have hne : hd.1.var ≠ v := hv hd (List.mem_cons_self)
      rw [ih _ _ _ (fun p hp => hv p (List.mem_cons_of_mem _ hp))]
      simp only [Function.update_apply, ne_eq, hne.symm, not_false_eq_true, ite_false]

/-- `processClauseLits` preserves ρ₀ at variables not in the literal list. -/
lemma processClauseLits_rho_stable {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) (v : Fin n) (hv : ∀ p ∈ lits, p.1.var ≠ v) :
    (processClauseLits lits path ρ₀ σ).2.1 v = ρ₀ v := by
  induction lits generalizing path ρ₀ σ with
  | nil => simp [processClauseLits]
  | cons hd tl ih =>
    cases path with
    | nil => simp [processClauseLits]
    | cons p ps =>
      simp only [processClauseLits]
      have hne : hd.1.var ≠ v := hv hd (List.mem_cons_self)
      rw [ih _ _ _ (fun p hp => hv p (List.mem_cons_of_mem _ hp))]
      simp only [Function.update_apply, ne_eq, hne.symm, not_false_eq_true, ite_false]

/-- `processClauseLits` never makes ρ₀ become `none`. -/
lemma processClauseLits_rho_ne_none {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) (v : Fin n) (hv : ρ₀ v ≠ none) :
    (processClauseLits lits path ρ₀ σ).2.1 v ≠ none := by
  induction lits generalizing path ρ₀ σ with
  | nil => simpa [processClauseLits]
  | cons hd tl ih =>
    cases path with
    | nil => simpa [processClauseLits]
    | cons p ps =>
      simp only [processClauseLits]
      apply ih
      simp only [Function.update_apply]
      split
      · simp
      · exact hv

/-! ## Encoder γ stability -/

/-- The encoder's γ preserves σ at variables that are non-free under ρ₀. -/
lemma encode_go_fst_nonfree {n : ℕ} (f : DNF n) (w : ℕ)
    (fuel : ℕ) (path : List (Fin n × Bool)) (ρ₀ σ : Restriction n)
    (acc : List (ℕ × Bool)) (v : Fin n) (hv : ρ₀ v ≠ none) :
    (razborovEncode.go f w fuel path ρ₀ σ acc).1 v = σ v := by
  induction fuel generalizing path ρ₀ σ acc with
  | zero =>
    cases path with
    | nil => simp [razborovEncode.go]
    | cons _ _ => simp [razborovEncode.go]
  | succ fuel ih =>
    cases path with
    | nil => simp [razborovEncode.go]
    | cons step rest =>
      simp only [razborovEncode.go]
      split
      · rfl
      · next t _ =>
        generalize hfli :
          List.filter (fun (x : Literal n × ℕ) => decide (x.1.var ∈ Restriction.freeVars ρ₀))
            (List.zipIdx t) = fli
        match fli with
        | [] => simp
        | fl :: fls =>
          have hfree : ∀ p ∈ (fl :: fls), ρ₀ p.1.var = none := by
            intro p hp
            have hm : p ∈ List.filter
                (fun (x : Literal n × ℕ) => decide (x.1.var ∈ Restriction.freeVars ρ₀))
                (List.zipIdx t) := hfli ▸ hp
            simp [List.mem_filter, Restriction.freeVars, Finset.mem_filter,
                  Option.isNone_iff_eq_none] at hm
            exact hm.2
          have hne : ∀ p ∈ (fl :: fls), p.1.var ≠ v :=
            fun p hp heq => hv (heq ▸ hfree p hp)
          rw [ih _ _ _ _ (processClauseLits_rho_ne_none _ _ _ _ _ hv)]
          exact processClauseLits_sigma_stable _ _ _ _ _ hne

/-! ## Accumulator lemmas -/

/-- The encoder's `go` with accumulator decomposes. -/
lemma encode_go_acc {n : ℕ} (f : DNF n) (w : ℕ)
    (fuel : ℕ) (path : List (Fin n × Bool)) (ρ₀ σ : Restriction n)
    (acc : List (ℕ × Bool)) :
    razborovEncode.go f w fuel path ρ₀ σ acc =
    let r := razborovEncode.go f w fuel path ρ₀ σ []
    (r.1, acc ++ r.2) := by
  induction fuel generalizing path ρ₀ σ acc with
  | zero =>
    cases path <;> simp [razborovEncode.go]
  | succ fuel ih =>
    cases path with
    | nil => simp [razborovEncode.go]
    | cons step rest =>
      simp only [razborovEncode.go]
      split
      · simp
      · split
        · simp
        · rw [ih, ih (acc := _ ++ _)]
          simp [List.append_assoc]

/-- The encoder's `.1` is independent of the accumulator. -/
lemma encode_go_fst_acc {n : ℕ} (f : DNF n) (w fuel : ℕ)
    (path : List (Fin n × Bool)) (ρ₀ σ : Restriction n) (acc : List (ℕ × Bool)) :
    (razborovEncode.go f w fuel path ρ₀ σ acc).1 =
    (razborovEncode.go f w fuel path ρ₀ σ []).1 := by
  have := encode_go_acc f w fuel path ρ₀ σ acc; rw [this]

/-! ## Decoder preservation lemmas -/

/-- `processEntries` preserves `none`. -/
lemma processEntries_preserves_none {n : ℕ}
    (t : Term n) (w : ℕ) (σ ρ₀ : Restriction n) (aux : List (ℕ × Bool))
    (v : Fin n) (hv : σ v = none) :
    (razborovDecode.processEntries t w σ ρ₀ aux).1 v = none := by
  induction aux generalizing σ ρ₀ with
  | nil => simp [razborovDecode.processEntries, hv]
  | cons entry rest ih =>
    simp only [razborovDecode.processEntries]
    split
    · exact hv
    · split
      · exact hv
      · apply ih
        simp only [Function.update_apply]
        split
        · rfl
        · exact hv

lemma decode_go_preserves_none {n : ℕ} (f : DNF n) (w : ℕ)
    (fuel : ℕ) (σ ρ₀ : Restriction n) (aux : List (ℕ × Bool))
    (v : Fin n) (hv : σ v = none) :
    (razborovDecode.go f w fuel σ ρ₀ aux).1 v = none := by
  induction fuel generalizing σ ρ₀ aux with
  | zero =>
    cases aux <;> simp [razborovDecode.go, hv]
  | succ fuel ih =>
    cases aux with
    | nil => simp [razborovDecode.go, hv]
    | cons entry restAux =>
      simp only [razborovDecode.go]
      split
      · exact hv
      · next t _ =>
        apply ih
        exact processEntries_preserves_none t w σ ρ₀ _ v hv

/-! ## processClauseLits σ-independence -/

/-- `processClauseLits` outputs `.1`, `.2.1`, `.2.2.2` are independent of σ. -/
lemma processClauseLits_sigma_indep {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ₁ σ₂ : Restriction n) :
    (processClauseLits lits path ρ₀ σ₁).1 = (processClauseLits lits path ρ₀ σ₂).1 ∧
    (processClauseLits lits path ρ₀ σ₁).2.1 = (processClauseLits lits path ρ₀ σ₂).2.1 ∧
    (processClauseLits lits path ρ₀ σ₁).2.2.2 = (processClauseLits lits path ρ₀ σ₂).2.2.2 := by
  induction lits generalizing path ρ₀ σ₁ σ₂ with
  | nil => simp [processClauseLits]
  | cons hd tl ih =>
    cases path with
    | nil => simp [processClauseLits]
    | cons p ps =>
      simp only [processClauseLits]
      obtain ⟨h1, h2, h3⟩ := ih ps _ _ _
      exact ⟨h1, h2, congrArg _ h3⟩

/-- The `.2` component of `razborovEncode.go` is independent of the `σ` argument. -/
lemma encode_go_snd_sigma_indep {n : ℕ} (f : DNF n) (w fuel : ℕ)
    (path : List (Fin n × Bool)) (ρ₀ σ₁ σ₂ : Restriction n) :
    (razborovEncode.go f w fuel path ρ₀ σ₁ []).2 =
    (razborovEncode.go f w fuel path ρ₀ σ₂ []).2 := by
  induction fuel generalizing path ρ₀ σ₁ σ₂ with
  | zero => cases path <;> simp [razborovEncode.go]
  | succ fuel ih =>
    cases path with
    | nil => simp [razborovEncode.go]
    | cons step rest =>
      simp only [razborovEncode.go]
      split
      · rfl
      · split
        · rfl
        · next fl fls _ =>
          have hindep := processClauseLits_sigma_indep (fl :: fls) (step :: rest) ρ₀ σ₁ σ₂
          obtain ⟨hpath, hrho, haux_eq⟩ := hindep
          have hacc₁ := encode_go_acc f w fuel
            (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ₁).1
            (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ₁).2.1
            (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ₁).2.2.1
            ((processClauseLits (fl :: fls) (step :: rest) ρ₀ σ₁).2.2.2 ++ [(w, false)])
          have hacc₂ := encode_go_acc f w fuel
            (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ₂).1
            (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ₂).2.1
            (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ₂).2.2.1
            ((processClauseLits (fl :: fls) (step :: rest) ρ₀ σ₂).2.2.2 ++ [(w, false)])
          simp only [hacc₁, hacc₂, List.nil_append]
          rw [haux_eq, hpath, hrho]
          exact congrArg _ (ih _ _ _ _)

/-! ## processClauseLits aux entry analysis -/

/-- Entries in `processClauseLits`'s aux correspond to literals from the input list. -/
lemma processClauseLits_aux_entries_from_lits {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) (e : ℕ × Bool) (he : e ∈ (processClauseLits lits path ρ₀ σ).2.2.2) :
    ∃ li ∈ lits, e.1 = li.2 := by
  induction lits generalizing path ρ₀ σ with
  | nil => simp [processClauseLits] at he
  | cons hd tl ih =>
    cases path with
    | nil => simp [processClauseLits] at he
    | cons p ps =>
      simp only [processClauseLits, List.mem_cons] at he
      rcases he with ⟨rfl, rfl⟩ | he
      · exact ⟨hd, .head _, rfl⟩
      · obtain ⟨li, hli, hidx⟩ := ih _ _ _ he
        exact ⟨li, List.mem_cons_of_mem _ hli, hidx⟩

/-- For non-free `v`, no entry in `pcl.2.2.2` targets `v`. -/
lemma processClauseLits_aux_ne_nonfree {n : ℕ}
    (t : Term n) (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) (v : Fin n)
    (hmem : ∀ p ∈ lits, p ∈ t.zipIdx)
    (hne_var : ∀ p ∈ lits, p.1.var ≠ v) :
    ∀ e ∈ (processClauseLits lits path ρ₀ σ).2.2.2,
    ∀ (l : Literal n) (rest : List (Literal n)),
    t.drop e.1 = l :: rest → l.var ≠ v := by
  intro e he l rest hdrop
  obtain ⟨li, hli, hidx⟩ := processClauseLits_aux_entries_from_lits lits path ρ₀ σ e he
  have hli_zip := hmem li hli
  obtain ⟨rest', hdrop'⟩ := zipIdx_drop_spec t li.1 li.2 hli_zip
  rw [hidx] at hdrop; rw [hdrop'] at hdrop
  have : l = li.1 := (List.cons.inj hdrop |>.1).symm
  rw [this]
  exact hne_var li hli

/-- All entries reference free literal variables. -/
lemma processClauseLits_aux_vars_free {n : ℕ}
    (t : Term n) (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) (e : ℕ × Bool)
    (he : e ∈ (processClauseLits lits path ρ₀ σ).2.2.2)
    (hmem : ∀ p ∈ lits, p ∈ t.zipIdx)
    (hfree : ∀ p ∈ lits, ρ₀ p.1.var = none) :
    ∀ (l : Literal n) (rest : List (Literal n)),
      t.drop e.1 = l :: rest → ρ₀ l.var = none := by
  obtain ⟨li, hli, hidx⟩ := processClauseLits_aux_entries_from_lits lits path ρ₀ σ e he
  obtain ⟨rest', hdrop'⟩ := zipIdx_drop_spec t li.1 li.2 (hmem li hli)
  intro l rest hdrop
  rw [hidx] at hdrop; rw [hdrop'] at hdrop
  have : l = li.1 := (List.cons.inj hdrop |>.1).symm
  rw [this]; exact hfree li hli

/-! ## Foldl stability lemmas -/

/-- The σ-foldl preserves `v` when no entry targets `v`. -/
lemma foldl_sigma_stable {n : ℕ} (t : Term n)
    (entries : List (ℕ × Bool)) (σ : Restriction n) (v : Fin n)
    (hne : ∀ e ∈ entries, ∀ (l : Literal n) (rest : List (Literal n)),
      t.drop e.1 = l :: rest → l.var ≠ v) :
    entries.foldl (fun σ (e : ℕ × Bool) =>
      match t.drop e.1 with | [] => σ | l :: _ => Function.update σ l.var none) σ v
    = σ v := by
  induction entries generalizing σ with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl_cons]
    have hne_e := hne e (List.mem_cons_self)
    have hne_es : ∀ e' ∈ es, _ := fun e' he' => hne e' (List.mem_cons_of_mem _ he')
    match h : t.drop e.1 with
    | [] => exact ih _ hne_es
    | l :: _ =>
      rw [ih _ hne_es]
      simp only [Function.update_apply, ne_eq, (hne_e l _ h).symm, not_false_eq_true, ite_false]

/-- The ρ₀-foldl preserves `v` when no entry targets `v`. -/
lemma foldl_rho_stable {n : ℕ} (t : Term n)
    (entries : List (ℕ × Bool)) (ρ₀ : Restriction n) (v : Fin n)
    (hne : ∀ e ∈ entries, ∀ (l : Literal n) (rest : List (Literal n)),
      t.drop e.1 = l :: rest → l.var ≠ v) :
    entries.foldl (fun ρ₀ (e : ℕ × Bool) =>
      match t.drop e.1 with | [] => ρ₀ | l :: _ => Function.update ρ₀ l.var (some e.2)) ρ₀ v
    = ρ₀ v := by
  induction entries generalizing ρ₀ with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl_cons]
    have hne_e := hne e (List.mem_cons_self)
    have hne_es : ∀ e' ∈ es, _ := fun e' he' => hne e' (List.mem_cons_of_mem _ he')
    match h : t.drop e.1 with
    | [] => exact ih _ hne_es
    | l :: _ =>
      rw [ih _ hne_es]
      simp only [Function.update_apply, ne_eq, (hne_e l _ h).symm, not_false_eq_true, ite_false]

/-- The σ-foldl preserves `none`. -/
lemma foldl_sigma_preserves_none {n : ℕ} (t : Term n)
    (entries : List (ℕ × Bool)) (σ : Restriction n) (v : Fin n) (hv : σ v = none) :
    entries.foldl (fun σ (e : ℕ × Bool) =>
      match t.drop e.1 with | [] => σ | l :: _ => Function.update σ l.var none) σ v = none := by
  induction entries generalizing σ with
  | nil => simpa
  | cons e es ih =>
    simp only [List.foldl_cons]
    apply ih
    match h : t.drop e.1 with
    | [] => simp [h, hv]
    | l :: _ =>
      simp only [Function.update_apply]
      split
      · exact rfl
      · exact hv

/-! ## processClauseLits foldl interaction lemmas -/

/-- If `pcl.2.1 v ≠ none` but `ρ₀ v = none`, the σ-foldl produces `none` at `v`. -/
lemma processClauseLits_foldl_sigma_none {n : ℕ} (t : Term n)
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ σ_dec : Restriction n) (v : Fin n)
    (hmem : ∀ p ∈ lits, p ∈ t.zipIdx)
    (hfree : ρ₀ v = none)
    (hset : (processClauseLits lits path ρ₀ σ).2.1 v ≠ none) :
    (processClauseLits lits path ρ₀ σ).2.2.2.foldl (fun σ (e : ℕ × Bool) =>
      match t.drop e.1 with | [] => σ | l :: _ => Function.update σ l.var none) σ_dec v
    = none := by
  induction lits generalizing path ρ₀ σ σ_dec with
  | nil => simp [processClauseLits] at hset; exact absurd hfree hset
  | cons hd tl ih =>
    cases path with
    | nil => simp [processClauseLits] at hset; exact absurd hfree hset
    | cons p ps =>
      simp only [processClauseLits, List.foldl_cons]
      obtain ⟨drop_rest, hdrop⟩ := zipIdx_drop_spec t hd.1 hd.2
        (hmem hd (.head _))
      simp only [hdrop]
      by_cases heq : hd.1.var = v
      · subst heq; exact foldl_sigma_preserves_none t _ _ _
          (by rw [Function.update_apply, if_pos rfl])
      · exact ih ps _ _ (Function.update σ_dec hd.1.var none)
          (fun p hp => hmem p (.tail _ hp))
          (by rwa [Function.update_apply, if_neg (Ne.symm heq)])
          (by simp only [processClauseLits] at hset; exact hset)

/-- The ρ₀-foldl agrees with `pcl.2.1` when initial values agree. -/
lemma processClauseLits_foldl_rho_eq {n : ℕ} (t : Term n)
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ ρ₀_dec : Restriction n) (v : Fin n)
    (hmem : ∀ p ∈ lits, p ∈ t.zipIdx)
    (hinit : ρ₀ v = ρ₀_dec v) :
    (processClauseLits lits path ρ₀ σ).2.2.2.foldl (fun ρ₀ (e : ℕ × Bool) =>
      match t.drop e.1 with | [] => ρ₀ | l :: _ => Function.update ρ₀ l.var (some e.2)) ρ₀_dec v
    = (processClauseLits lits path ρ₀ σ).2.1 v := by
  induction lits generalizing path ρ₀ σ ρ₀_dec with
  | nil => simp [processClauseLits, hinit]
  | cons hd tl ih =>
    cases path with
    | nil => simp [processClauseLits, hinit]
    | cons p ps =>
      simp only [processClauseLits, List.foldl_cons]
      obtain ⟨drop_rest, hdrop⟩ := zipIdx_drop_spec t hd.1 hd.2 (hmem hd (.head _))
      simp only [hdrop]
      exact ih ps _ _ _
        (fun q hq => hmem q (.tail _ hq))
        (by simp only [Function.update_apply]; split <;> simp_all)

/-- Variant when initial values may differ but `v` gets set by PCL. -/
lemma processClauseLits_foldl_rho_eq_of_set {n : ℕ} (t : Term n)
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ ρ₀_dec : Restriction n) (v : Fin n)
    (hmem : ∀ p ∈ lits, p ∈ t.zipIdx)
    (hfree : ρ₀ v = none)
    (hset : (processClauseLits lits path ρ₀ σ).2.1 v ≠ none) :
    (processClauseLits lits path ρ₀ σ).2.2.2.foldl (fun ρ₀ (e : ℕ × Bool) =>
      match t.drop e.1 with | [] => ρ₀ | l :: _ => Function.update ρ₀ l.var (some e.2)) ρ₀_dec v
    = (processClauseLits lits path ρ₀ σ).2.1 v := by
  induction lits generalizing path ρ₀ σ ρ₀_dec with
  | nil => simp [processClauseLits] at hset; exact absurd hfree hset
  | cons hd tl ih =>
    cases path with
    | nil => simp [processClauseLits] at hset; exact absurd hfree hset
    | cons p ps =>
      simp only [processClauseLits, List.foldl_cons]
      obtain ⟨drop_rest, hdrop⟩ := zipIdx_drop_spec t hd.1 hd.2 (hmem hd (.head _))
      simp only [hdrop]
      by_cases heq : hd.1.var = v
      · exact processClauseLits_foldl_rho_eq t tl ps _ _ _ v
          (fun q hq => hmem q (.tail _ hq))
          (by simp only [Function.update_apply, if_pos heq.symm])
      · exact ih ps _ _ _
          (fun q hq => hmem q (.tail _ hq))
          (by rwa [Function.update_apply, if_neg (Ne.symm heq)])
          (by simp only [processClauseLits] at hset; exact hset)

/-- Contrapositive of rho_stable. -/
lemma processClauseLits_no_target_of_rho_none {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) (v : Fin n)
    (hfree : ρ₀ v = none)
    (hnone : (processClauseLits lits path ρ₀ σ).2.1 v = none)
    (hlen : lits.length ≤ path.length) :
    ∀ p ∈ lits, p.1.var ≠ v := by
  induction lits generalizing path ρ₀ σ with
  | nil => intro p hp; simp at hp
  | cons hd tl ih =>
    cases path with
    | nil => simp at hlen
    | cons step rest =>
      simp only [processClauseLits] at hnone
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp_tl
      · intro hpv
        have hne : (Function.update ρ₀ p.1.var (some step.2)) v ≠ none := by
          rw [Function.update_apply, if_pos hpv.symm]; exact Option.some_ne_none _
        exact absurd hnone (processClauseLits_rho_ne_none tl rest _ _ _ hne)
      · by_cases heq : hd.1.var = v
        · have hne : (Function.update ρ₀ hd.1.var (some step.2)) v ≠ none := by
            rw [Function.update_apply, if_pos heq.symm]; exact Option.some_ne_none _
          exact absurd hnone (processClauseLits_rho_ne_none tl rest _ _ _ hne)
        · exact ih rest _ _ (by rwa [Function.update_apply, if_neg (Ne.symm heq)]) hnone
            (by simp [List.length_cons] at hlen ⊢; omega) p hp_tl

/-! ## processClauseLits σ at v -/

/-- `processClauseLits` σ output at `v` depends only on initial σ at `v`. -/
lemma processClauseLits_sigma_at_v {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ₁ σ₂ : Restriction n) (v : Fin n) (hv : σ₁ v = σ₂ v) :
    (processClauseLits lits path ρ₀ σ₁).2.2.1 v =
    (processClauseLits lits path ρ₀ σ₂).2.2.1 v := by
  induction lits generalizing path ρ₀ σ₁ σ₂ with
  | nil => simp [processClauseLits, hv]
  | cons hd tl ih =>
    cases path with
    | nil => simp [processClauseLits, hv]
    | cons p ps =>
      simp only [processClauseLits]
      apply ih
      simp only [Function.update_apply]
      split_ifs <;> [rfl; exact hv]

/-
If `ρ₀ v = none` and `processClauseLits` leaves `ρ₀` at `v` as `none`,
    then `σ` at `v` is also unchanged. This holds because `processClauseLits`
    updates `ρ₀` and `σ` at exactly the same variables in lockstep.
-/
lemma processClauseLits_sigma_none_of_rho_none {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) (v : Fin n)
    (hfree : ρ₀ v = none)
    (h : (processClauseLits lits path ρ₀ σ).2.1 v = none) :
    (processClauseLits lits path ρ₀ σ).2.2.1 v = σ v := by
  induction' lits with hd tl ih generalizing path ρ₀ σ;
  · cases path <;> aesop;
  · rcases path with ( _ | ⟨ x, path ⟩ ) <;> simp +decide [ processClauseLits ] at h ⊢;
    by_cases hvar : hd.1.var = v;
    · exact absurd h ( by exact SwitchingLemma2.processClauseLits_rho_ne_none _ _ _ _ _ ( by aesop ) );
    · convert ih path ( Function.update ρ₀ hd.1.var ( some x.2 ) ) ( Function.update σ hd.1.var ( some !hd.1.neg ) ) _ h using 1;
      · rw [ Function.update_apply ] ; aesop;
      · rw [ Function.update_apply ] ; aesop

/-! ## Encoder σ-independence at free variables -/

/-- The encoder's `.1` (γ) at a free variable `v` is independent of initial σ. -/
lemma encode_go_fst_sigma_indep_at_free {n : ℕ} (f : DNF n) (w fuel : ℕ)
    (path : List (Fin n × Bool)) (ρ₀ σ₁ σ₂ : Restriction n) (v : Fin n)
    (hfree : ρ₀ v = none) (h₁ : σ₁ v = none) (h₂ : σ₂ v = none) :
    (razborovEncode.go f w fuel path ρ₀ σ₁ []).1 v =
    (razborovEncode.go f w fuel path ρ₀ σ₂ []).1 v := by
  induction fuel generalizing path ρ₀ σ₁ σ₂ with
  | zero => cases path <;> simp [razborovEncode.go, h₁, h₂]
  | succ fuel ih =>
    cases path with
    | nil => simp [razborovEncode.go, h₁, h₂]
    | cons step rest =>
      simp only [razborovEncode.go]
      split
      · simp [h₁, h₂]
      · split
        · simp [h₁, h₂]
        · next fl fls _ =>
          obtain ⟨hpath, hrho, _⟩ :=
            processClauseLits_sigma_indep (fl :: fls) (step :: rest) ρ₀ σ₁ σ₂
          conv_lhs => rw [encode_go_fst_acc]
          conv_rhs => rw [encode_go_fst_acc]
          rw [hpath, hrho]
          by_cases hv : (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ₂).2.1 v = none
          · have hσ₁_eq : (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ₁).2.2.1 v = none :=
              (processClauseLits_sigma_none_of_rho_none _ _ _ _ _ hfree
                (hrho ▸ hv)) ▸ h₁ ▸ rfl
            have hσ₂_eq : (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ₂).2.2.1 v = none :=
              (processClauseLits_sigma_none_of_rho_none _ _ _ _ _ hfree hv) ▸ h₂ ▸ rfl
            exact ih _ _ _ _ hv hσ₁_eq hσ₂_eq
          · rw [encode_go_fst_nonfree f w fuel _ _ _ [] v hv,
                encode_go_fst_nonfree f w fuel _ _ _ [] v hv]
            exact processClauseLits_sigma_at_v _ _ _ _ _ v (by rw [h₁, h₂])

/-! ## processEntries characterization -/

/-- Characterization of `processEntries` on data from `processClauseLits`
    followed by a termination marker. -/
lemma processEntries_of_processClauseLits {n : ℕ}
    (t : Term n) (w : ℕ) (hw : t.length ≤ w)
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀_enc σ_enc σ_dec ρ₀_dec : Restriction n)
    (rest : List (ℕ × Bool))
    (hmem : ∀ p ∈ lits, p ∈ t.zipIdx) :
    let pcl := processClauseLits lits path ρ₀_enc σ_enc
    razborovDecode.processEntries t w σ_dec ρ₀_dec (pcl.2.2.2 ++ [(w, false)] ++ rest) =
    ( pcl.2.2.2.foldl (fun σ (e : ℕ × Bool) =>
        match t.drop e.1 with | [] => σ | l :: _ => Function.update σ l.var none) σ_dec,
      pcl.2.2.2.foldl (fun ρ₀ (e : ℕ × Bool) =>
        match t.drop e.1 with | [] => ρ₀ | l :: _ => Function.update ρ₀ l.var (some e.2)) ρ₀_dec,
      rest ) := by
  induction lits generalizing path ρ₀_enc σ_enc σ_dec ρ₀_dec with
  | nil =>
    simp only [processClauseLits, List.nil_append, List.foldl_nil]
    simp [razborovDecode.processEntries, show w ≥ w from le_refl w]
  | cons hd tl ih =>
    cases path with
    | nil =>
      simp only [processClauseLits, List.nil_append, List.foldl_nil]
      simp [razborovDecode.processEntries, show w ≥ w from le_refl w]
    | cons p ps =>
      simp only [processClauseLits]
      have hmem_hd : hd ∈ t.zipIdx :=
        hmem hd (.head _)
      have hidx_lt : hd.2 < w := by
        obtain ⟨_, hidx, _⟩ := List.mem_zipIdx hmem_hd
        simp at hidx; omega
      obtain ⟨drop_rest, hdrop⟩ := zipIdx_drop_spec t hd.1 hd.2 hmem_hd
      simp only [List.cons_append, razborovDecode.processEntries,
                 show ¬(hd.2 ≥ w) from by omega, ↓reduceIte, hdrop]
      -- Unfold one step of the foldl on the RHS
      simp only [List.foldl_cons, hdrop]
      exact ih ps _ _ _ _ (fun q hq => hmem q (.tail _ hq))

/-
`processClauseLits` never sets σ at `l.var` to `some l.neg`,
    provided no literal in the list has `var = l.var` with a different `neg`.
-/
private lemma processClauseLits_sigma_ne_neg {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) (l : Literal n)
    (hnd : ∀ m ∈ lits, m.1.var = l.var → m.1 = l)
    (hσ : σ l.var ≠ some l.neg) :
    (processClauseLits lits path ρ₀ σ).2.2.1 l.var ≠ some l.neg := by
  induction lits generalizing path ρ₀ σ with
  | nil => simpa [processClauseLits]
  | cons hd tl ih =>
    cases path with
    | nil => simpa [processClauseLits]
    | cons p ps =>
      simp only [processClauseLits]
      apply ih ps _ _ (fun m hm => hnd m (List.mem_cons_of_mem _ hm))
      by_cases heq : hd.1.var = l.var
      · have hd_eq : hd.1 = l := hnd hd List.mem_cons_self heq
        rw [Function.update_apply, if_pos heq.symm, hd_eq]
        intro h
        injection h with h'
        cases hb : l.neg <;> (rw [hb] at h'; simp at h')
      · rw [Function.update_apply, if_neg (Ne.symm heq)]
        exact hσ

/-
If `(l, idx) ∈ lits` with unique var (by `hnd`) and
    `ρ₀ l.var = none` initially but `pcl.2.1 l.var = none` after,
    then the remaining path `pcl.1` must be `[]`.
    This is because `l` was not processed (path ran out before it).
-/
private lemma processClauseLits_path_nil_of_rho_none_and_mem {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) (l : Literal n) (idx : ℕ)
    (hl : (l, idx) ∈ lits)
    (hnd : ∀ m ∈ lits, m.1.var = l.var → m.1 = l)
    (hfree : ρ₀ l.var = none)
    (h : (processClauseLits lits path ρ₀ σ).2.1 l.var = none) :
    (processClauseLits lits path ρ₀ σ).1 = [] := by
  induction lits generalizing path ρ₀ σ with
  | nil => exact absurd hl (List.not_mem_nil)
  | cons hd tl ih =>
    cases path with
    | nil => simp [processClauseLits]
    | cons p ps =>
      simp only [processClauseLits] at h ⊢
      -- Reduce: in either case of membership, apply IH with updated ρ₀
      rcases List.mem_cons.mp hl with hl_eq | hl_tl
      · -- hl : (l, idx) = hd, so hd.1 = l and hd.1.var = l.var
        -- After update, ρ₀ at l.var = some p.2 ≠ none, so PCL rho at l.var ≠ none
        have hd_var : hd.1.var = l.var := by rw [← hl_eq]
        exfalso
        apply processClauseLits_rho_ne_none tl ps _ _ l.var _ h
        rw [Function.update_apply, if_pos hd_var.symm]
        exact Option.some_ne_none _
      · -- hl : (l, idx) ∈ tl. Apply IH.
        by_cases heq : hd.1.var = l.var
        · -- hd.1.var = l.var, so after update ρ₀ l.var = some p.2 ≠ none. Contradicts h.
          exfalso
          apply processClauseLits_rho_ne_none tl ps _ _ l.var _ h
          rw [Function.update_apply, if_pos heq.symm]
          exact Option.some_ne_none _
        · exact ih ps _ _ hl_tl
            (fun m hm => hnd m (List.mem_cons_of_mem _ hm))
            (by rw [Function.update_apply, if_neg (Ne.symm heq)]; exact hfree)
            h

/-! ## Encoder first-clause preservation -/

/-
The encoder does not kill the first clause found by `find?`.
-/
set_option maxHeartbeats 800000 in
lemma encode_go_not_kills_first_clause {n : ℕ} (f : DNF n) (w : ℕ)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (enc_fuel : ℕ) (path : List (Fin n × Bool)) (ρ₀ σ : Restriction n)
    (hE : ∀ v, ρ₀ v = none → σ v = none)
    (t : Term n)
    (hfind : f.find? (fun t => decide (¬Term.killedBy t ρ₀)) = some t)
    (l : Literal n) (hl : l ∈ t) (hfree : ρ₀ l.var = none) :
    (razborovEncode.go f w enc_fuel path ρ₀ σ []).1 l.var ≠ some l.neg := by
  induction' enc_fuel with enc_fuel ih generalizing path ρ₀ σ <;> simp_all +decide [ razborovEncode.go ];
  · cases path <;> simp_all +decide [ SwitchingLemma2.razborovEncode.go ];
  · rcases path with ( _ | ⟨ step, rest ⟩ );
    · rw [ razborovEncode.go ] ; aesop;
    · obtain ⟨fl, fls, hfl⟩ : ∃ fl fls, (t.zipIdx).filter (fun ⟨l, _⟩ => decide (l.var ∈ ρ₀.freeVars)) = fl :: fls := by
        obtain ⟨k, hk⟩ : ∃ k, l = t.get k ∧ k.val < t.length := by
          have := List.mem_iff_get.mp hl; aesop;
        have h_mem : (l, k.val) ∈ (t.zipIdx).filter (fun ⟨l, _⟩ => decide (l.var ∈ ρ₀.freeVars)) := by
          simp +decide [ hk, hfree, Restriction.freeVars ];
          grind;
        exact List.exists_cons_of_ne_nil ( by rintro h; simp +decide [ h ] at h_mem );
      -- By definition of `processClauseLits`, we know that `pcl.2.1 l.var = none` or `pcl.2.1 l.var ≠ none`.
      by_cases hpcl : (SwitchingLemma2.processClauseLits (fl :: fls) (step :: rest) ρ₀ σ).2.1 l.var = none;
      · have hpcl_path : (SwitchingLemma2.processClauseLits (fl :: fls) (step :: rest) ρ₀ σ).1 = [] := by
          apply SwitchingLemma2.processClauseLits_path_nil_of_rho_none_and_mem;
          rotate_left;
          rotate_left;
          exact hfree;
          exact hpcl;
          exact ( List.idxOf l t );
          · replace hfl := congr_arg List.toFinset hfl; rw [ Finset.ext_iff ] at hfl; specialize hfl ( l, List.idxOf l t ) ; simp_all +decide [ List.mem_iff_get ] ;
            contrapose! hfl; simp_all +decide [ Fin.exists_iff ] ;
            refine Or.inl ⟨ ⟨ ?_, ?_ ⟩, ?_, ?_ ⟩;
            · grind;
            · unfold Restriction.freeVars; aesop;
            · exact fun h => hfl ⟨ 0, Nat.zero_lt_succ _ ⟩ ( by aesop );
            · exact fun i => fun hi => hfl ⟨ i + 1, by linarith [ Fin.is_lt i ] ⟩ ( by simpa [ Fin.add_def, Nat.mod_eq_of_lt ] using hi );
          · grind +splitImp;
        rw [ SwitchingLemma2.razborovEncode.go ];
        rw [ show List.find? ( fun t => decide ¬Term.killedBy t ρ₀ ) f = some t from by simpa using hfind ];
        simp +decide [ hpcl_path, hfl ];
        rw [ SwitchingLemma2.razborovEncode.go ];
        simp only []
        have hnd_lits : ∀ m ∈ (fl :: fls), m.1.var = l.var → m.1 = l := by
          intro m hm hmv
          have hm' := hfl ▸ hm
          have hmz := (List.mem_filter.mp hm').1
          obtain ⟨_, hi, heq⟩ := List.mem_zipIdx hmz
          simp at hi heq
          have hmt : m.1 ∈ t := heq ▸ List.getElem_mem (by omega)
          exact hnd t (List.mem_of_find?_eq_some hfind) m.1 hmt l hl hmv
        exact processClauseLits_sigma_ne_neg _ _ _ _ _ hnd_lits (by rw [hE _ hfree]; simp)
      · have hnd_lits : ∀ m ∈ (fl :: fls), m.1.var = l.var → m.1 = l := by
          intro m hm hmv
          have hm' := hfl ▸ hm
          have hmz := (List.mem_filter.mp hm').1
          obtain ⟨_, hi, heq⟩ := List.mem_zipIdx hmz
          simp at hi heq
          have hmt : m.1 ∈ t := heq ▸ List.getElem_mem (by omega)
          exact hnd t (List.mem_of_find?_eq_some hfind) m.1 hmt l hl hmv
        have hkey : (razborovEncode.go f w enc_fuel
            (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ).1
            (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ).2.1
            (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ).2.2.1
            ((processClauseLits (fl :: fls) (step :: rest) ρ₀ σ).2.2.2 ++ [(w, false)])).1 l.var
            = (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ).2.2.1 l.var := by
          rw [encode_go_fst_acc]
          exact encode_go_fst_nonfree f w enc_fuel _ _ _ [] l.var (by push_neg at hpcl; exact hpcl)
        rw [ SwitchingLemma2.razborovEncode.go ];
        rw [ show List.find? ( fun t => decide ¬Term.killedBy t ρ₀ ) f = some t from by simpa using hfind ] ; simp +decide [ hfl ] ;
        rw [hkey]
        exact processClauseLits_sigma_ne_neg _ _ _ _ _ hnd_lits (by rw [hE _ hfree]; simp)

/-! ## processClauseLits rho ne none of mem -/

/-- If `p ∈ lits` and `p.1.var = v`, then `pcl.2.1 v ≠ none`
    (provided there are enough path entries). -/
lemma processClauseLits_rho_ne_none_of_mem {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) (v : Fin n)
    (p : Literal n × ℕ) (hp : p ∈ lits) (hpv : p.1.var = v)
    (hlen : lits.length ≤ path.length) :
    (processClauseLits lits path ρ₀ σ).2.1 v ≠ none := by
  induction lits generalizing path ρ₀ σ with
  | nil => simp at hp
  | cons hd tl ih =>
    cases path with
    | nil => simp at hlen
    | cons step rest =>
      simp only [processClauseLits]
      rcases List.mem_cons.mp hp with rfl | hp_tl
      · -- p = hd, so hd.1.var = v, Function.update sets ρ₀ at v to some
        apply processClauseLits_rho_ne_none
        rw [Function.update_apply, if_pos hpv.symm]
        exact Option.some_ne_none _
      · exact ih rest _ _ hp_tl (by simp [List.length_cons] at hlen ⊢; omega)

/-! ## Round-trip base case -/

/-- Base-case helper: when the encoder returns `(σ, [])`, the decoder returns σ. -/
lemma roundtrip_base {n : ℕ} (f : DNF n) (w : ℕ)
    (ρ₀ σ σ_dec ρ₀_dec : Restriction n) (dec_fuel : ℕ)
    (hE : ∀ v, ρ₀ v = none → σ v = none)
    (hA : ∀ v, ρ₀ v = none → σ_dec v = σ v)
    (hC : ∀ v, ρ₀ v ≠ none → σ_dec v = σ v) :
    (razborovDecode.go f w dec_fuel σ_dec ρ₀_dec []).1 = σ := by
  cases dec_fuel with
  | zero => simp [razborovDecode.go]; funext v; by_cases h : ρ₀ v = none <;> simp_all
  | succ _ => simp [razborovDecode.go]; funext v; by_cases h : ρ₀ v = none <;> simp_all

end SwitchingLemma2
