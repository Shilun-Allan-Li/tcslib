
/-! Liveness pairs (gsw-6b-u18-u19, C6, owner Asymptotic.lean), appended to the owner's own probe.
Owner pair: a foreign definition (`levelTerm`, LeveledSecurity.lean) read by `rfl` and through its
reader `levelTerm_eq`. Helper pair (the new public helper `Parameters.ofFamily_columns_le`): the
width of `ofFamily` read through its body by `rfl` (negative), and through the two `simps` readers
(positive), and the helper itself used sealed (positive). -/

-- NEG levelTerm by rfl
example (P : TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Parameters) (χ : TCSlib.Cryptography.LWE.Noise) (L : ℕ) (μ : Bool) (e : Fin L)
    (j : Fin P.columns) (D : TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.LeveledView P L → Unit → Bool) :
    TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.levelTerm P χ L μ e j D =
      TCSlib.Cryptography.LWE.decisionAdvantage P.lwe χ (TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.levelReduction P χ L μ e j true D) +
        TCSlib.Cryptography.LWE.decisionAdvantage P.lwe χ
          (TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.levelReduction P χ L μ e j false D) +
        2 * (P.columns * TCSlib.Cryptography.Encryption.PublicKey.Regev.extractionError P.lwe) :=
  rfl
-- POS levelTerm through levelTerm_eq
example (P : TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Parameters) (χ : TCSlib.Cryptography.LWE.Noise) (L : ℕ) (μ : Bool) (e : Fin L)
    (j : Fin P.columns) (D : TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.LeveledView P L → Unit → Bool) :
    TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.levelTerm P χ L μ e j D =
      TCSlib.Cryptography.LWE.decisionAdvantage P.lwe χ (TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.levelReduction P χ L μ e j true D) +
        TCSlib.Cryptography.LWE.decisionAdvantage P.lwe χ
          (TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.levelReduction P χ L μ e j false D) +
        2 * (P.columns * TCSlib.Cryptography.Encryption.PublicKey.Regev.extractionError P.lwe) :=
  TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.levelTerm_eq P χ L μ e j D
-- NEG Parameters.ofFamily by rfl (helper pair)
example (F : TCSlib.Cryptography.LWE.Family) (κ : ℕ) :
    (TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Parameters.ofFamily F κ).columns =
      ((F.parameters κ).dimension + 1) * F.residueBits.eval κ :=
  rfl
-- POS Parameters.ofFamily through its readers (helper pair)
example (F : TCSlib.Cryptography.LWE.Family) (κ : ℕ) :
    (TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Parameters.ofFamily F κ).columns =
      ((F.parameters κ).dimension + 1) * F.residueBits.eval κ := by
  rw [TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Parameters.columns_eq, TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Parameters.ofFamily_lwe, TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Parameters.ofFamily_width]
-- POS Parameters.ofFamily_columns_le used sealed (helper pair)
example (F : TCSlib.Cryptography.LWE.Family) (κ : ℕ) :
    (TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Parameters.ofFamily F κ).columns ≤
      (F.dimensionBound.eval κ + 1) * F.residueBits.eval κ :=
  TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Parameters.ofFamily_columns_le F κ
