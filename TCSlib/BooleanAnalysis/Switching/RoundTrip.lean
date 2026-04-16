import TCSlib.BooleanAnalysis.Switching.EncodingProperties

/-!
# Round-Trip Proof

The main round-trip theorem: decoding the Razborov encoding recovers the
original restriction.
-/

open Classical

namespace SwitchingLemma2

variable {n : ℕ}

/-! ## Invariant case lemmas -/

/-- If pcl.2.1 v = none, then ρ₀ v = none. -/
lemma pcl_none_implies_rho_free {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) (v : Fin n)
    (hv' : (processClauseLits lits path ρ₀ σ).2.1 v = none) :
    ρ₀ v = none := by
  by_contra h; push_neg at h
  exact absurd hv' (processClauseLits_rho_ne_none lits path ρ₀ σ v h)

/-- If the encoder finds `t_clause` as the first non-killed clause under `ρ₀`,
    then the decoder's restriction `ρ₀_dec` also finds `t_clause` first. -/
lemma find_clause_preserved_in_encode {n : ℕ}
    (f : DNF n) (w : ℕ)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (enc_fuel : ℕ) (path : List (Fin n × Bool)) (ρ₀ σ ρ₀_dec : Restriction n)
    (t_clause : Term n)
    (hfind_enc : f.find? (fun t => decide (¬Term.killedBy t ρ₀)) = some t_clause)
    (hE : ∀ v, ρ₀ v = none → σ v = none)
    (hB : ∀ v, ρ₀ v = none →
      ρ₀_dec v = (razborovEncode.go f w enc_fuel path ρ₀ σ []).1 v)
    (hD : ∀ v, ρ₀ v ≠ none → ρ₀_dec v = ρ₀ v) :
    f.find? (fun t => decide (¬Term.killedBy t ρ₀_dec)) = some t_clause := by
  apply first_clause_preserved f ρ₀ ρ₀_dec t_clause hfind_enc hD
  intro ⟨l, hl_mem, hl_killed⟩
  simp only [Literal.killedBy] at hl_killed
  by_cases hfv : ρ₀ l.var = none
  · rw [hB l.var hfv] at hl_killed
    exact encode_go_not_kills_first_clause f w hnd enc_fuel
      path ρ₀ σ hE t_clause hfind_enc l hl_mem hfv hl_killed
  · rw [hD l.var hfv] at hl_killed
    have hkill : Term.killedBy t_clause ρ₀ := ⟨l, hl_mem, hl_killed⟩
    have hnkill := List.find?_some hfind_enc
    simp at hnkill
    exact absurd hkill hnkill

/-- The `fl :: fls` list from filtering free-var literals of `t_clause` preserves
    both the zipIdx membership and the freeness of each literal's variable. -/
lemma mem_filter_freeVars_zipIdx {n : ℕ} (ρ₀ : Restriction n)
    (t_clause : List (Literal n)) (p : Literal n × ℕ)
    (hp : p ∈ List.filter
      (fun (x : Literal n × ℕ) => decide (x.1.var ∈ Restriction.freeVars ρ₀))
      (List.zipIdx t_clause)) :
    p ∈ t_clause.zipIdx ∧ ρ₀ p.1.var = none := by
  refine ⟨(List.mem_filter.mp hp).1, ?_⟩
  have hfree := (List.mem_filter.mp hp).2
  simp [Restriction.freeVars, Finset.mem_filter, Option.isNone_iff_eq_none] at hfree
  exact hfree

/-! ## Aux entries don't target free-remaining vars -/

/-- If `pcl.2.1 v = none`, then no aux entry targets `v`. -/
lemma processClauseLits_aux_ne_of_pcl_none {n : ℕ}
    (t : Term n) (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) (v : Fin n)
    (hmem : ∀ p ∈ lits, p ∈ t.zipIdx)
    (hnone : (processClauseLits lits path ρ₀ σ).2.1 v = none) :
    ∀ e ∈ (processClauseLits lits path ρ₀ σ).2.2.2,
    ∀ (l : Literal n) (rest : List (Literal n)),
    t.drop e.1 = l :: rest → l.var ≠ v := by
  revert hnone;
  induction' lits with lits ih generalizing path ρ₀ σ;
  · intro _ e he _ _ _; simp [processClauseLits] at he
  · rcases path with ( _ | ⟨ step, path ⟩ ) <;> simp_all +decide [ processClauseLits ];
    intro hnone
    apply And.intro;
    · intro l rest hdrop hvar
      have hvar_eq : lits.1.var = v := by
        have hzip : (lits.1, lits.2) ∈ List.zipIdx t := hmem.left
        have hzip : ∃ rest, t.drop lits.2 = lits.1 :: rest := by
          exact zipIdx_drop_spec t lits.1 lits.2 hzip;
        grind +splitImp;
      exact absurd hnone ( by erw [ hvar_eq ] ; exact fun h => by have := processClauseLits_rho_ne_none ih path ( Function.update ρ₀ v ( some step.2 ) ) ( Function.update σ v ( some !lits.1.neg ) ) v; aesop )
    · grind +splitIndPred

/-! ## Encoder first-component connection -/

/-- The encoder's .1 computed with (fuel+1) and step::rest equals
    the recursive encoder's .1 (when the clause is found). -/
lemma encode_go_fst_eq_rec {n : ℕ} (f : DNF n) (w fuel : ℕ)
    (step : Fin n × Bool) (rest : List (Fin n × Bool))
    (ρ₀ σ : Restriction n)
    (t_clause : Term n)
    (hfind : f.find? (fun t => decide (¬Term.killedBy t ρ₀)) = some t_clause)
    (fl : Literal n × ℕ) (fls : List (Literal n × ℕ))
    (hfli_eq : List.filter (fun (x : Literal n × ℕ) => decide (x.1.var ∈ Restriction.freeVars ρ₀))
      (List.zipIdx t_clause) = fl :: fls) :
    let pcl := processClauseLits (fl :: fls) (step :: rest) ρ₀ σ
    (razborovEncode.go f w (fuel + 1) (step :: rest) ρ₀ σ []).1 =
    (razborovEncode.go f w fuel pcl.1 pcl.2.1 pcl.2.2.1 []).1 := by
  cases' h : List.find? ( fun t => !Term.killedBy t ρ₀ ) f with t <;> simp_all +decide [ SwitchingLemma2.razborovEncode.go ];
  rw [ SwitchingLemma2.encode_go_fst_acc ]

/-! ## Round-trip invariant lemmas -/

/-
Invariant hC': σ_fold agrees with σ at non-free vars of pcl.2.1
-/
lemma roundtrip_inv_hC' {n : ℕ}
    (t_clause : Term n)
    (lits : List (Literal n × ℕ))
    (path : List (Fin n × Bool))
    (ρ₀ σ σ_dec : Restriction n)
    (hfree_lits : ∀ p ∈ lits, ρ₀ p.1.var = none)
    (hmem_zip : ∀ p ∈ lits, p ∈ t_clause.zipIdx)
    (hE : ∀ v, ρ₀ v = none → σ v = none)
    (hC : ∀ v, ρ₀ v ≠ none → σ_dec v = σ v)
    (v : Fin n)
    (hv : (processClauseLits lits path ρ₀ σ).2.1 v ≠ none) :
    (processClauseLits lits path ρ₀ σ).2.2.2.foldl
      (fun σ' (e : ℕ × Bool) =>
        match t_clause.drop e.1 with | [] => σ' | l :: _ => Function.update σ' l.var none)
      σ_dec v = σ v := by
  by_cases hv' : ρ₀ v = none <;> simp_all +decide ;
  · exact?;
  · convert foldl_sigma_stable t_clause ( processClauseLits lits path ρ₀ σ |> Prod.snd |> Prod.snd |> Prod.snd ) σ_dec v _ using 1;
    · rw [ hC v hv' ];
    · apply_rules [ SwitchingLemma2.processClauseLits_aux_ne_nonfree ];
      · exact fun p hp => hmem_zip _ _ hp;
      · grind +ring

/-
Invariant hD': ρ₀_fold agrees with pcl.2.1 at non-free vars
-/
lemma roundtrip_inv_hD' {n : ℕ}
    (t_clause : Term n)
    (lits : List (Literal n × ℕ))
    (path : List (Fin n × Bool))
    (ρ₀ σ ρ₀_dec : Restriction n)
    (hfree_lits : ∀ p ∈ lits, ρ₀ p.1.var = none)
    (hmem_zip : ∀ p ∈ lits, p ∈ t_clause.zipIdx)
    (hD : ∀ v, ρ₀ v ≠ none → ρ₀_dec v = ρ₀ v)
    (v : Fin n)
    (hv : (processClauseLits lits path ρ₀ σ).2.1 v ≠ none) :
    (processClauseLits lits path ρ₀ σ).2.2.2.foldl
      (fun ρ₀' (e : ℕ × Bool) =>
        match t_clause.drop e.1 with | [] => ρ₀' | l :: _ => Function.update ρ₀' l.var (some e.2))
      ρ₀_dec v = (processClauseLits lits path ρ₀ σ).2.1 v := by
  by_cases hfree : ρ₀ v = none;
  · convert SwitchingLemma2.processClauseLits_foldl_rho_eq_of_set t_clause lits path ρ₀ σ ρ₀_dec v hmem_zip hfree hv using 1;
  · have hnone : ∀ p ∈ lits, p.1.var ≠ v := by
      grind +ring;
    convert foldl_rho_stable t_clause ( processClauseLits lits path ρ₀ σ |>.2.2.2 ) ρ₀_dec v _ using 1;
    · rw [ hD v hfree, processClauseLits_rho_stable lits path ρ₀ σ v hnone ];
    · exact?

/-! ## Main round-trip theorem -/

/-- Generalized round-trip: the decoder recovers σ from the encoder output. -/
private lemma go_roundtrip_gen {n : ℕ} (f : DNF n) (w : ℕ) (hw : f.width ≤ w)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (enc_fuel : ℕ) (path : List (Fin n × Bool)) (ρ₀ σ : Restriction n)
    (σ_dec ρ₀_dec : Restriction n) (dec_fuel : ℕ)
    (hE : ∀ v, ρ₀ v = none → σ v = none)
    (hA : ∀ v, ρ₀ v = none → σ_dec v = (razborovEncode.go f w enc_fuel path ρ₀ σ []).1 v)
    (hB : ∀ v, ρ₀ v = none → ρ₀_dec v = (razborovEncode.go f w enc_fuel path ρ₀ σ []).1 v)
    (hC : ∀ v, ρ₀ v ≠ none → σ_dec v = σ v)
    (hD : ∀ v, ρ₀ v ≠ none → ρ₀_dec v = ρ₀ v)
    (hfuel : dec_fuel ≥ (razborovEncode.go f w enc_fuel path ρ₀ σ []).2.length + 1) :
    (razborovDecode.go f w dec_fuel σ_dec ρ₀_dec
      (razborovEncode.go f w enc_fuel path ρ₀ σ []).2).1 = σ := by
  set enc := razborovEncode.go f w enc_fuel path ρ₀ σ [] with henc_def
  have base : enc = (σ, []) →
      (razborovDecode.go f w dec_fuel σ_dec ρ₀_dec enc.2).1 = σ := by
    intro heq
    rw [show enc.2 = [] from by rw [heq]]
    exact roundtrip_base f w ρ₀ σ σ_dec ρ₀_dec dec_fuel hE
      (fun v hv => by rw [hA v hv, show enc.1 v = σ v from by rw [heq]]) hC
  induction enc_fuel generalizing path ρ₀ σ σ_dec ρ₀_dec dec_fuel with
  | zero =>
    cases path <;> (simp only [razborovEncode.go] at henc_def; exact base henc_def)
  | succ fuel ih =>
    cases path with
    | nil => simp only [razborovEncode.go] at henc_def; exact base henc_def
    | cons step rest =>
      simp only [razborovEncode.go] at henc_def
      revert henc_def; split
      · intro henc_def; exact base henc_def
      · rename_i t_clause hfind_enc
        intro henc_def
        generalize hfli_eq :
          List.filter (fun (x : Literal n × ℕ) => decide (x.1.var ∈ Restriction.freeVars ρ₀))
            (List.zipIdx t_clause) = fli
        revert henc_def; rw [hfli_eq]; intro henc_def
        match fli with
        | [] => exact base henc_def
        | fl :: fls =>
          simp only [List.nil_append] at henc_def
          set pcl := processClauseLits (fl :: fls) (step :: rest) ρ₀ σ with hpcl_def
          set rec_enc := razborovEncode.go f w fuel pcl.1 pcl.2.1 pcl.2.2.1 [] with hrec_def
          have henc_acc := encode_go_acc f w fuel pcl.1 pcl.2.1 pcl.2.2.1
            (pcl.2.2.2 ++ [(w, false)])
          have henc_eq : enc = (rec_enc.1, (pcl.2.2.2 ++ [(w, false)]) ++ rec_enc.2) :=
            henc_def.trans henc_acc
          have haux : enc.2 = pcl.2.2.2 ++ [(w, false)] ++ rec_enc.2 := by
            have := congrArg Prod.snd henc_eq; simpa [List.append_assoc] using this
          have hfli_spec : ∀ p ∈ (fl :: fls),
              p ∈ t_clause.zipIdx ∧ ρ₀ p.1.var = none := by
            intro p hp; rw [← hfli_eq] at hp
            exact mem_filter_freeVars_zipIdx ρ₀ t_clause p hp
          have hmem_zip : ∀ p ∈ (fl :: fls), p ∈ t_clause.zipIdx :=
            fun p hp => (hfli_spec p hp).1
          have hfree_lits : ∀ p ∈ (fl :: fls), ρ₀ p.1.var = none :=
            fun p hp => (hfli_spec p hp).2
          have htw : t_clause.length ≤ w :=
            le_trans (term_length_le_width f t_clause (List.mem_of_find?_eq_some hfind_enc)) hw
          have hfind_dec : f.find? (fun t => decide (¬Term.killedBy t ρ₀_dec)) =
              some t_clause :=
            find_clause_preserved_in_encode f w hnd (fuel + 1) (step :: rest)
              ρ₀ σ ρ₀_dec t_clause hfind_enc hE hB hD
          have hpe := processEntries_of_processClauseLits t_clause w htw
            (fl :: fls) (step :: rest) ρ₀ σ σ_dec ρ₀_dec rec_enc.2 hmem_zip
          rw [haux]
          have hpcl_aux_ne : pcl.2.2.2 ≠ [] := by
            simp only [hpcl_def, processClauseLits]; exact List.cons_ne_nil _ _
          obtain ⟨hd_aux, tl_aux, hpcl_cons⟩ := List.exists_cons_of_ne_nil hpcl_aux_ne
          obtain ⟨df, rfl⟩ : ∃ k, dec_fuel = k + 1 := ⟨dec_fuel - 1, by omega⟩
          rw [hpcl_cons]
          simp only [List.cons_append, razborovDecode.go, hfind_dec]
          have hreassoc : hd_aux :: (tl_aux ++ [(w, false)] ++ rec_enc.2) =
              pcl.2.2.2 ++ [(w, false)] ++ rec_enc.2 := by
            simp only [hpcl_cons, List.cons_append, List.append_assoc]
          rw [hreassoc, hpe]
          -- Define the foldl'd restrictions (without set, to avoid opacity issues)
          have hsigma_indep : rec_enc.2 =
              (razborovEncode.go f w fuel pcl.1 pcl.2.1 σ []).2 :=
            encode_go_snd_sigma_indep f w fuel pcl.1 pcl.2.1 pcl.2.2.1 σ
          rw [hsigma_indep]
          -- Key: enc.1 = rec_enc.1
          have henc1_eq : enc.1 = rec_enc.1 := by
            have := congrArg Prod.fst henc_eq; simp at this; exact this
          -- Helper: σ_indep for rec_enc
          have hrec_sigma_indep : ∀ v, pcl.2.1 v = none →
              rec_enc.1 v = (razborovEncode.go f w fuel pcl.1 pcl.2.1 σ []).1 v := by
            intro v hv
            exact encode_go_fst_sigma_indep_at_free f w fuel pcl.1 pcl.2.1
              pcl.2.2.1 σ v hv
              (by rw [processClauseLits_sigma_none_of_rho_none _ _ _ _ v
                       (pcl_none_implies_rho_free _ _ ρ₀ σ v hv) hv,
                       hE v (pcl_none_implies_rho_free _ _ ρ₀ σ v hv)])
              (hE v (pcl_none_implies_rho_free _ _ ρ₀ σ v hv))
          -- Now apply ih
          -- The goal has tuple projections that need simplification
          -- Goal: (go f w df (foldl_σ, foldl_ρ, enc'.2).1 (foldl_σ, foldl_ρ, enc'.2).2.1 enc'.2).1 = σ
          -- which is: (go f w df foldl_σ foldl_ρ enc'.2).1 = σ
          apply ih pcl.1 pcl.2.1 σ
            (pcl.2.2.2.foldl (fun σ (e : ℕ × Bool) =>
              match t_clause.drop e.1 with | [] => σ | l :: _ => Function.update σ l.var none) σ_dec)
            (pcl.2.2.2.foldl (fun ρ₀ (e : ℕ × Bool) =>
              match t_clause.drop e.1 with | [] => ρ₀ | l :: _ => Function.update ρ₀ l.var (some e.2)) ρ₀_dec)
            df
          -- (1) hE': pcl.2.1 v = none → σ v = none
          · exact fun v hv => hE v (pcl_none_implies_rho_free _ _ ρ₀ σ v hv)
          -- (2) hC': pcl.2.1 v ≠ none → σ_fold v = σ v
          · exact fun v hv => roundtrip_inv_hC' t_clause _ _ ρ₀ σ σ_dec hfree_lits hmem_zip hE hC v hv
          -- (3) hD': pcl.2.1 v ≠ none → ρ₀_fold v = pcl.2.1 v
          · exact fun v hv => roundtrip_inv_hD' t_clause _ _ ρ₀ σ ρ₀_dec hfree_lits hmem_zip hD v hv
          -- (4) hA': pcl.2.1 v = none → σ_fold v = (go f w fuel pcl.1 pcl.2.1 σ []).1 v
          · intro v hv
            have h1 : pcl.2.2.2.foldl (fun σ (e : ℕ × Bool) =>
              match t_clause.drop e.1 with | [] => σ | l :: _ => Function.update σ l.var none) σ_dec v
              = σ_dec v :=
              foldl_sigma_stable t_clause _ _ _
                (processClauseLits_aux_ne_of_pcl_none t_clause _ _ _ _ v hmem_zip hv)
            rw [h1, hA v (pcl_none_implies_rho_free _ _ ρ₀ σ v hv), henc1_eq]
            exact hrec_sigma_indep v hv
          -- (5) hB': pcl.2.1 v = none → ρ₀_fold v = (go f w fuel pcl.1 pcl.2.1 σ []).1 v
          · intro v hv
            have h1 : pcl.2.2.2.foldl (fun ρ₀ (e : ℕ × Bool) =>
              match t_clause.drop e.1 with | [] => ρ₀ | l :: _ => Function.update ρ₀ l.var (some e.2)) ρ₀_dec v
              = ρ₀_dec v :=
              foldl_rho_stable t_clause _ _ _
                (processClauseLits_aux_ne_of_pcl_none t_clause _ _ _ _ v hmem_zip hv)
            rw [h1, hB v (pcl_none_implies_rho_free _ _ ρ₀ σ v hv), henc1_eq]
            exact hrec_sigma_indep v hv
          -- (6) fuel bound
          · rw [← hsigma_indep]
            have : enc.2.length = pcl.2.2.2.length + 1 + rec_enc.2.length := by
              simp only [haux, List.length_append, List.length_cons, List.length_nil]
            have : pcl.2.2.2.length ≥ 1 := by rw [hpcl_cons]; simp
            omega
          -- (7) rfl
          · rfl
          -- (8) base case
          · intro heq
            have h_enc2_nil : (razborovEncode.go f w fuel pcl.1 pcl.2.1 σ []).2 = [] :=
              congrArg Prod.snd heq
            rw [h_enc2_nil]
            apply roundtrip_base f w pcl.2.1 σ _ _ df
            · exact fun v hv => hE v (pcl_none_implies_rho_free _ _ ρ₀ σ v hv)
            · intro v hv
              have h1 := foldl_sigma_stable t_clause pcl.2.2.2 σ_dec v
                (processClauseLits_aux_ne_of_pcl_none t_clause _ _ _ _ v hmem_zip hv)
              have h2 := hA v (pcl_none_implies_rho_free _ _ ρ₀ σ v hv)
              have h5 : (razborovEncode.go f w fuel pcl.1 pcl.2.1 σ []).1 v = σ v :=
                congrFun (congrArg Prod.fst heq) v
              calc _ = σ_dec v := h1
                _ = enc.1 v := h2
                _ = rec_enc.1 v := congrFun henc1_eq v
                _ = (razborovEncode.go f w fuel pcl.1 pcl.2.1 σ []).1 v := hrec_sigma_indep v hv
                _ = σ v := h5
            · exact fun v hv => roundtrip_inv_hC' t_clause _ _ ρ₀ σ σ_dec hfree_lits hmem_zip hE hC v hv

/-- Go-level round-trip. -/
private lemma go_roundtrip {n : ℕ} (f : DNF n) (w : ℕ) (hw : f.width ≤ w)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (enc_fuel : ℕ) (path : List (Fin n × Bool)) (ρ : Restriction n) :
    let enc := razborovEncode.go f w enc_fuel path ρ ρ []
    (razborovDecode.go f w (enc.2.length + 1) enc.1 enc.1 enc.2).1 = ρ := by
  exact go_roundtrip_gen f w hw hnd enc_fuel path ρ ρ
    (razborovEncode.go f w enc_fuel path ρ ρ []).1
    (razborovEncode.go f w enc_fuel path ρ ρ []).1
    ((razborovEncode.go f w enc_fuel path ρ ρ []).2.length + 1)
    (fun v hv => hv)
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun v hv => encode_go_fst_nonfree f w enc_fuel path ρ ρ [] v hv)
    (fun v hv => encode_go_fst_nonfree f w enc_fuel path ρ ρ [] v hv)
    (le_refl _)

/-- The round-trip: decoding the encoding of ρ recovers ρ. -/
lemma razborovDecode_encode {n : ℕ} (f : DNF n) (w d : ℕ) (ρ : Restriction n)
    (_hbad : IsBadRestriction f.eval d ρ) (hw : f.width ≤ w)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂) :
    razborovDecode f w (razborovEncode f w d ρ).1 (razborovEncode f w d ρ).2 = ρ := by
  unfold razborovDecode razborovEncode
  exact go_roundtrip f w hw hnd _ _ ρ

/-- **Injectivity**: the encoding is injective on bad restrictions. -/
theorem razborovEncode_injective {n : ℕ} (f : DNF n) (w d : ℕ)
    (ρ₁ ρ₂ : Restriction n)
    (hbad₁ : IsBadRestriction f.eval d ρ₁) (hbad₂ : IsBadRestriction f.eval d ρ₂)
    (hw : f.width ≤ w)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (henc : razborovEncode f w d ρ₁ = razborovEncode f w d ρ₂) :
    ρ₁ = ρ₂ := by
  rw [← razborovDecode_encode f w d ρ₁ hbad₁ hw hnd,
      ← razborovDecode_encode f w d ρ₂ hbad₂ hw hnd, henc]

end SwitchingLemma2
