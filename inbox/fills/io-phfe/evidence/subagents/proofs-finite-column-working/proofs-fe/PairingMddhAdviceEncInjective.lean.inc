/-- The advice word is injective on its index and scalar matrices. Technical glue.

**Proof sketch.** Split the fixed-width blocks. The one-hot word recovers the hybrid index.
Use `BB1Machine.order_le_two_pow` and the fixed order equality for a generated instance;
then apply `Encoding.Modular.encodeMatrix_injective` to each scalar block. -/
theorem mddhAdviceEnc_injective (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (d ℓ : PolyExpr) (κ : ℕ) :
    Function.Injective (G.mddhAdviceEnc p hp d ℓ κ) := by
  letI : NeZero (p κ) := orderSchedule_neZero G p hp κ
  intro ω₁ ω₂ h
  -- Separate the fixed public metadata and then the fixed-length scalar blocks.
  simp only [G.mddhAdviceEnc_eq p hp d ℓ κ] at h
  rcases Prod.mk.inj (pairEncode_injective h) with ⟨_, h₁⟩
  rcases Prod.mk.inj (pairEncode_injective h₁) with ⟨_, h₂⟩
  rcases Prod.mk.inj (pairEncode_injective h₂) with ⟨_, hBody⟩
  simp only [List.append_assoc] at hBody
  have hIndexLen :=
    (List.length_ofFn (f := fun i : Fin (d.eval κ + 1) => decide (i = ω₁.1))).trans
      (List.length_ofFn (f := fun i : Fin (d.eval κ + 1) => decide (i = ω₂.1))).symm
  rcases List.append_inj hBody hIndexLen with ⟨hIndexWord, hBlocks⟩
  have hLLen :=
    (Encoding.Modular.encodeMatrix_length (G.wG.eval κ) ω₁.2.1).trans
      (Encoding.Modular.encodeMatrix_length (G.wG.eval κ) ω₂.2.1).symm
  rcases List.append_inj hBlocks hLLen with ⟨hLWord, hTail⟩
  have hSLen :=
    (Encoding.Modular.encodeMatrix_length (G.wG.eval κ) ω₁.2.2.1).trans
      (Encoding.Modular.encodeMatrix_length (G.wG.eval κ) ω₂.2.2.1).symm
  rcases List.append_inj hTail hSLen with ⟨hSWord, hUWord⟩
  -- The one-hot bit at the first advice index identifies that index.
  have hIndex : ω₁.1 = ω₂.1 :=
    of_decide_eq_true
      ((congrFun (List.ofFn_injective hIndexWord) ω₁.1).symm.trans
        (decide_eq_true (Eq.refl ω₁.1)))
  -- A generated instance supplies the existing no-truncation bound for each scalar word.
  have hWidth : p κ ≤ 2 ^ G.wG.eval κ := ?_
  swap
  · rw [← hp κ (fun _ => false), G.inst_eq κ (fun _ => false)]
    exact TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Machine.order_le_two_pow
      G κ (G.desc κ (fun _ => false))
  have hL : ω₁.2.1 = ω₂.2.1 :=
    Encoding.Modular.encodeMatrix_injective
      (q := p κ) (rows := ℓ.eval κ) (columns := 3) (G.wG.eval κ) hWidth hLWord
  have hS : ω₁.2.2.1 = ω₂.2.2.1 :=
    Encoding.Modular.encodeMatrix_injective
      (q := p κ) (rows := 2) (columns := d.eval κ) (G.wG.eval κ) hWidth hSWord
  have hU : ω₁.2.2.2 = ω₂.2.2.2 :=
    Encoding.Modular.encodeMatrix_injective
      (q := p κ) (rows := ℓ.eval κ) (columns := d.eval κ) (G.wG.eval κ) hWidth hUWord
  exact Prod.ext hIndex (Prod.ext hL (Prod.ext hS hU))
