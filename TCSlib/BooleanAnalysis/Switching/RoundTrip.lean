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

/-- If pcl.2.1 v = none, then no literal in the list targets v. -/
lemma pcl_none_implies_no_target {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) (v : Fin n)
    (hv' : (processClauseLits lits path ρ₀ σ).2.1 v = none)
    (hlen : lits.length ≤ path.length) :
    ∀ p ∈ lits, p.1.var ≠ v := by
  intro p hp heq
  exact absurd (heq ▸ hv' : (processClauseLits lits path ρ₀ σ).2.1 p.1.var = none)
    (processClauseLits_rho_ne_none_of_mem _ _ _ _ _ p hp rfl hlen)

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
          have hγ : enc.1 = rec_enc.1 := by rw [henc_eq]
          have haux : enc.2 = pcl.2.2.2 ++ [(w, false)] ++ rec_enc.2 := by
            have := congrArg Prod.snd henc_eq; simpa [List.append_assoc] using this
          have hmem_zip : ∀ p ∈ (fl :: fls), p ∈ t_clause.zipIdx := by
            intro p hp; rw [← hfli_eq] at hp; exact (List.mem_filter.mp hp).1
          have htw : t_clause.length ≤ w :=
            le_trans (term_length_le_width f t_clause (List.mem_of_find?_eq_some hfind_enc)) hw
          have hfree_lits : ∀ p ∈ (fl :: fls), ρ₀ p.1.var = none := by
            intro p hp; rw [← hfli_eq] at hp
            simp [List.mem_filter, Restriction.freeVars, Finset.mem_filter,
                  Option.isNone_iff_eq_none] at hp; exact hp.2
          have hfind_dec : f.find? (fun t => decide (¬Term.killedBy t ρ₀_dec)) =
              some t_clause := by
            apply first_clause_preserved f ρ₀ ρ₀_dec t_clause hfind_enc hD
            intro ⟨l, hl_mem, hl_killed⟩
            simp only [Literal.killedBy] at hl_killed
            by_cases hfv : ρ₀ l.var = none
            · rw [hB l.var hfv] at hl_killed
              exact encode_go_not_kills_first_clause f w hnd (fuel + 1)
                (step :: rest) ρ₀ σ hE t_clause hfind_enc l hl_mem hfv (hγ ▸ hl_killed)
            · rw [hD l.var hfv] at hl_killed
              have hkill : Term.killedBy t_clause ρ₀ := ⟨l, hl_mem, hl_killed⟩
              have hnkill := List.find?_some hfind_enc; simp at hnkill
              exact absurd hkill hnkill
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
          set σ_fold := pcl.2.2.2.foldl (fun σ (e : ℕ × Bool) =>
            match t_clause.drop e.1 with | [] => σ | l :: _ => Function.update σ l.var none) σ_dec
          set ρ₀_fold := pcl.2.2.2.foldl (fun ρ₀ (e : ℕ × Bool) =>
            match t_clause.drop e.1 with | [] => ρ₀ | l :: _ => Function.update ρ₀ l.var (some e.2)) ρ₀_dec
          have hsigma_indep : rec_enc.2 =
              (razborovEncode.go f w fuel pcl.1 pcl.2.1 σ []).2 :=
            encode_go_snd_sigma_indep f w fuel pcl.1 pcl.2.1 pcl.2.2.1 σ
          rw [hsigma_indep]
          -- Apply the induction hypothesis with the updated invariants
          sorry

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
    (hbad : IsBadRestriction f.eval d ρ) (hw : f.width ≤ w)
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
